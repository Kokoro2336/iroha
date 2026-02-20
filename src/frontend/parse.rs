use crate::base::SymbolTable;
use crate::base::Type;
use crate::debug::{error, info};
use crate::frontend::ast::*;
use crate::utils::arena::Arena;

/**
 * A module which provides a variety of utilities for parsing.
 */
pub struct Parser {
    // This symbol table is used for constant folding during parsing, we don't need to add variants.
    pub syms: SymbolTable<String, NodeId>,
    pub ast: AST,
}

impl Parser {
    pub fn new() -> Self {
        Parser {
            syms: SymbolTable::new(),
            ast: AST::new(),
        }
    }

    // Check if we are currently in the global scope.
    pub fn is_global(&self) -> bool {
        self.syms.current_scope() == 1
    }

    pub fn take(self) -> AST {
        self.ast
    }

    fn take_node(&mut self, id: NodeId) -> Node {
        self.ast
            .remove(id)
            .unwrap_or_else(|e| panic!("Parser take_node failed at {}: {}", id, e))
    }

    // early constant folding optimization
    // NOTE: fold consumes the ownership of node.
    pub fn fold(&mut self, node: Node) -> Node {
        match node {
            Node::BinaryOp { lhs, op, rhs, .. } => {
                let lhs_node = self.take_node(lhs);
                let rhs_node = self.take_node(rhs);
                let lhs = self.fold(lhs_node);
                let rhs = self.fold(rhs_node);

                match (lhs, rhs) {
                    (
                        Node::Literal(Literal::Int(lhs_val)),
                        Node::Literal(Literal::Int(rhs_val)),
                    ) => {
                        let result = match op {
                            Op::Add => lhs_val + rhs_val,
                            Op::Sub => lhs_val - rhs_val,
                            Op::Mul => lhs_val * rhs_val,
                            Op::Div => lhs_val / rhs_val,
                            Op::Mod => lhs_val % rhs_val,
                            _ => panic!("Unsupported operation for constant folding: {:?}", op),
                        };
                        Node::Literal(Literal::Int(result))
                    }
                    (
                        Node::Literal(Literal::Float(lhs_val)),
                        Node::Literal(Literal::Float(rhs_val)),
                    ) => {
                        let result = match op {
                            Op::Add => lhs_val + rhs_val,
                            Op::Sub => lhs_val - rhs_val,
                            Op::Mul => lhs_val * rhs_val,
                            Op::Div => lhs_val / rhs_val,
                            _ => panic!("Unsupported operation for constant folding: {:?}", op),
                        };
                        Node::Literal(Literal::Float(result))
                    }
                    (
                        Node::Literal(Literal::Float(lhs_val)),
                        Node::Literal(Literal::Int(rhs_val)),
                    ) => {
                        let result = match op {
                            Op::Add => lhs_val + rhs_val as f32,
                            Op::Sub => lhs_val - rhs_val as f32,
                            Op::Mul => lhs_val * rhs_val as f32,
                            Op::Div => lhs_val / rhs_val as f32,
                            _ => panic!("Unsupported operation for constant folding: {:?}", op),
                        };
                        Node::Literal(Literal::Float(result))
                    }
                    (
                        Node::Literal(Literal::Int(lhs_val)),
                        Node::Literal(Literal::Float(rhs_val)),
                    ) => {
                        let result = match op {
                            Op::Add => lhs_val as f32 + rhs_val,
                            Op::Sub => lhs_val as f32 - rhs_val,
                            Op::Mul => lhs_val as f32 * rhs_val,
                            Op::Div => lhs_val as f32 / rhs_val,
                            _ => panic!("Unsupported operation for constant folding: {:?}", op),
                        };
                        Node::Literal(Literal::Float(result))
                    }
                    _ => panic!("Non-constant folding operation: {:?}", op),
                }
            }
            Node::UnaryOp { op, operand, .. } => {
                let operand_node = self.take_node(operand);
                let operand = self.fold(operand_node);

                match operand {
                    Node::Literal(Literal::Int(val)) => {
                        let result = match op {
                            Op::Plus => val,
                            Op::Minus => -val,
                            _ => {
                                panic!("Unsupported unary operation for constant folding: {:?}", op)
                            }
                        };
                        Node::Literal(Literal::Int(result))
                    }
                    Node::Literal(Literal::Float(val)) => {
                        let result = match op {
                            Op::Plus => val,
                            Op::Minus => -val,
                            _ => {
                                panic!("Unsupported unary operation for constant folding: {:?}", op)
                            }
                        };
                        Node::Literal(Literal::Float(result))
                    }
                    Node::Literal(Literal::String(_)) => {
                        unreachable!(
                            "Unsupported unary operation for constant folding on String: {:?}",
                            op
                        );
                    }
                    _ => panic!("Non-constant folding unary operation: {:?}", op),
                }
            }
            Node::Literal(lit) => Node::Literal(lit),
            Node::VarAccess { name, .. } => {
                if let Some(const_val) = self.syms.get(&name) {
                    match self.ast[*const_val] {
                        Node::Literal(Literal::Int(val)) => Node::Literal(Literal::Int(val)),
                        Node::Literal(Literal::Float(val)) => Node::Literal(Literal::Float(val)),
                        Node::Literal(Literal::String(_)) => {
                            unreachable!("String literal folding is not supported yet: {}", name)
                        }
                        _ => panic!("Variable {} is not a constant literal for folding", name),
                    }
                } else {
                    panic!("Undefined variable {} for folding", name);
                }
            }
            Node::ArrayAccess { name, indices, .. } => {
                let (typ, init_values) = if let Some(array_val) = self.syms.get(&name) {
                    match &self.ast[*array_val] {
                        Node::ConstArray {
                            typ, init_values, ..
                        } => (typ.clone(), init_values.clone()),
                        _ => panic!("ArrayAccess value is not ConstArray for folding"),
                    }
                } else {
                    panic!("Undefined array {} for folding", name);
                };

                let dims = match &typ {
                    Type::Array { dims, .. } => dims,
                    _ => panic!("ArrayAccess type is not Array"),
                };

                if indices.len() != dims.len() {
                    panic!(
                        "Array index dimension mismatch for folding: expected {}, found {}",
                        dims.len(),
                        indices.len()
                    );
                }

                let mut flat_index: usize = 0;
                for (i, index_node) in indices.into_iter().enumerate() {
                    let index = self.take_node(index_node);
                    let folded = self.fold(index);
                    let idx = match folded {
                        Node::Literal(Literal::Int(idx)) => idx as usize,
                        Node::Literal(Literal::Float(idx)) => {
                            panic!("Array index must be integer literal, found float: {}", idx)
                        }
                        Node::Literal(Literal::String(_)) => {
                            panic!("Array index must be integer literal, found string")
                        }
                        _ => panic!("Array index must be a constant literal for folding"),
                    };

                    let stride = if i + 1 >= dims.len() {
                        1usize
                    } else {
                        dims[(i + 1)..].iter().product::<u32>() as usize
                    };
                    flat_index += idx * stride;
                }

                if let Some(init_values) = init_values {
                    if let Some(val_id) = init_values.get(flat_index) {
                        match self.ast[*val_id] {
                            Node::Literal(Literal::Int(v)) => Node::Literal(Literal::Int(v)),
                            Node::Literal(Literal::Float(v)) => Node::Literal(Literal::Float(v)),
                            Node::Literal(Literal::String(ref s)) => {
                                Node::Literal(Literal::String(s.clone()))
                            }
                            _ => panic!(
                                "ArrayAccess folded value should be literal, got: {:?}",
                                self.ast[*val_id]
                            ),
                        }
                    } else {
                        panic!(
                            "Array index out of bounds for folding: index {}, size {}",
                            flat_index,
                            init_values.len()
                        );
                    }
                } else {
                    Node::Literal(Literal::Int(0))
                }
            }
            other => other,
        }
    }

    // 1. Unfold the RawDecls into separate declarations.
    // 2. Flatten the array.
    pub fn canonicalize(&mut self, node_id: NodeId) -> Vec<NodeId> {
        let node = self.take_node(node_id);
        let (aggr_typ, mutable, raw_decls) = match node {
            Node::RawDecl {
                typ,
                mutable,
                raw_decls,
            } => (typ, mutable, raw_decls),
            _ => panic!("canonicalize expects RawDecl"),
        };

        let mut new_nodes: Vec<NodeId> = vec![];

        for raw_decl in raw_decls {
            if raw_decl.const_exps.is_empty() {
                let mut init_value = raw_decl.init_val;

                if !mutable {
                    if let Some(init_val) = init_value {
                        let init_node = self.take_node(init_val);
                        let folded_init_val = self.fold(init_node);
                        let folded_init_id = self.ast.alloc(folded_init_val);
                        match self.ast[folded_init_id] {
                            Node::Literal(_) => {
                                self.syms.insert(raw_decl.ident.clone(), folded_init_id);
                                init_value = Some(folded_init_id);
                            }
                            _ => {
                                panic!(
                                    "Const variable {} must have a literal initial value",
                                    raw_decl.ident
                                );
                            }
                        }
                    } else {
                        panic!(
                            "Const variable {} must have an initial value",
                            raw_decl.ident
                        );
                    }
                }

                let var_decl = Node::VarDecl {
                    name: raw_decl.ident,
                    is_global: self.is_global(),
                    typ: aggr_typ.clone(),
                    mutable,
                    init_value,
                };
                new_nodes.push(self.ast.alloc(var_decl));
            } else {
                let mut dims: Vec<u32> = vec![];
                for exp_node in raw_decl.const_exps {
                    let node = self.take_node(exp_node);
                    let folded = self.fold(node);
                    if let Node::Literal(Literal::Int(int_node)) = folded {
                        dims.push(int_node as u32);
                    } else {
                        panic!("Array size must be a constant integer literal");
                    }
                }

                if mutable {
                    let init_values = if let Some(init_val) = raw_decl.init_val {
                        self.flatten(aggr_typ.clone(), dims.clone(), init_val)
                    } else {
                        None
                    };

                    let var_array = Node::VarArray {
                        name: raw_decl.ident,
                        is_global: self.is_global(),
                        typ: Type::Array {
                            base: Box::new(aggr_typ.clone()),
                            dims,
                        },
                        init_values,
                    };
                    new_nodes.push(self.ast.alloc(var_array));
                } else {
                    let init_val = raw_decl
                        .init_val
                        .expect("ConstArray should have an initial value for constant folding!");

                    let const_array = Node::ConstArray {
                        name: raw_decl.ident.clone(),
                        typ: Type::Array {
                            base: Box::new(aggr_typ.clone()),
                            dims: dims.clone(),
                        },
                        init_values: self.flatten(aggr_typ.clone(), dims, init_val),
                    };

                    let const_array_id = self.ast.alloc(const_array);
                    self.syms.insert(raw_decl.ident, const_array_id);
                    new_nodes.push(const_array_id);
                }
            }
        }

        new_nodes
    }

    fn flatten(
        &mut self,
        base_typ: Type,
        indices: Vec<u32>,
        node_id: NodeId,
    ) -> Option<Vec<NodeId>> {
        let node = self.take_node(node_id);
        let init_vals = if let Node::ArrayInitVal { init_vals } = node {
            if init_vals.is_empty() {
                return None;
            }
            init_vals
        } else {
            panic!("flatten can only process ArrayInitVal nodes");
        };

        let mut new_vals: Vec<NodeId> = vec![];
        let mut has_non_zero = false;

        let root = Node::ArrayInitVal { init_vals };
        self.flatten_rec(
            &base_typ,
            &indices,
            root,
            0,
            &mut new_vals,
            &mut has_non_zero,
        );

        let expected_size = indices
            .iter()
            .fold(1usize, |acc, index| acc * (*index as usize));
        if new_vals.len() != expected_size {
            error!(
                "Array has insufficient initializers: expected {}, found {}. \\nFlattened values: {:?}",
                expected_size,
                new_vals.len(),
                new_vals
            );
        }

        info!("Successfully flattened array: {:?}", new_vals);
        if !has_non_zero {
            None
        } else {
            Some(new_vals)
        }
    }

    fn flatten_rec(
        &mut self,
        base_typ: &Type,
        indices: &Vec<u32>,
        val: Node,
        depth: u32,
        new_vals: &mut Vec<NodeId>,
        has_non_zero: &mut bool,
    ) -> u32 {
        let mut filled_size: u32 = 0;

        match val {
            Node::ArrayInitVal { init_vals } => {
                info!("Catch ArrayInitVal at depth {}", depth);
                if new_vals.len() as u32 % indices.last().unwrap() != 0 {
                    panic!("Array has insufficient initializers");
                }

                let mut acc = 1;
                let mut idx = indices.len();
                for index in indices.iter().skip(depth as usize).rev() {
                    acc *= *index as usize;
                    if new_vals.len() % acc == 0 {
                        idx -= 1;
                    }
                }

                for child_id in init_vals {
                    let child = self.take_node(child_id);
                    filled_size += self.flatten_rec(
                        base_typ,
                        indices,
                        child,
                        depth + 1,
                        new_vals,
                        has_non_zero,
                    );
                }

                let to_be_filled =
                    indices[idx..indices.len()].iter().product::<u32>() - filled_size;

                for _ in 0..to_be_filled {
                    let zero = match base_typ {
                        Type::Int => Node::Literal(Literal::Int(0)),
                        Type::Float => Node::Literal(Literal::Float(0.0)),
                        _ => unreachable!(
                            "Only Int and Float types are supported in array initialization"
                        ),
                    };
                    new_vals.push(self.ast.alloc(zero));
                }

                filled_size += to_be_filled;
            }
            Node::Literal(lit) => {
                match lit {
                    Literal::Int(v) => {
                        if v != 0 {
                            *has_non_zero = true;
                        }
                        new_vals.push(self.ast.alloc(Node::Literal(Literal::Int(v))));
                    }
                    Literal::Float(v) => {
                        if v != 0.0 {
                            *has_non_zero = true;
                        }
                        new_vals.push(self.ast.alloc(Node::Literal(Literal::Float(v))));
                    }
                    _ => unreachable!(
                        "Only Int and Float literals are supported in array initialization"
                    ),
                }
                filled_size += 1;
            }
            other => {
                new_vals.push(self.ast.alloc(other));
                filled_size += 1;
            }
        }

        filled_size
    }
}
