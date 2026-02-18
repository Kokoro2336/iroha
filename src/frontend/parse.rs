use crate::base::SymbolTable;
use crate::base::Type;
use crate::debug::{error, info};
use crate::frontend::ast::*;
use crate::utils::{cast, cast_deref, cast_mut, is};

use std::cell::RefCell;
use tool::fix;

/**
 * A module which provides a variety of utilities for parsing.
 */
use crate::frontend::ast::{BinaryOp, Literal, Node, Op, UnaryOp};

pub struct Parser {
    // This symbol table is used for constant folding during parsing, we don't need to add variants.
    pub syms: SymbolTable<String, Box<dyn Node>>,
}

impl Parser {
    pub fn new() -> Self {
        Parser {
            syms: SymbolTable::new(),
        }
    }

    // Check if we are currently in the global scope.
    pub fn is_global(&self) -> bool {
        self.syms.current_scope() == 1
    }

    // early constant folding optimization
    pub fn fold(&mut self, mut node: Box<dyn Node>) -> Box<dyn Node> {
        if is::<BinaryOp>(&*node) {
            let bin_op = cast_deref::<BinaryOp>(node).unwrap();
            let lhs = self.fold(bin_op.lhs);
            let rhs = self.fold(bin_op.rhs);

            if is::<Literal>(&*lhs) && is::<Literal>(&*rhs) {
                let lhs_lit = cast_deref::<Literal>(lhs).unwrap();
                let rhs_lit = cast_deref::<Literal>(rhs).unwrap();

                match (*lhs_lit, *rhs_lit) {
                    (Literal::Int(lhs_val), Literal::Int(rhs_val)) => {
                        let result = match bin_op.op {
                            Op::Add => lhs_val + rhs_val,
                            Op::Sub => lhs_val - rhs_val,
                            Op::Mul => lhs_val * rhs_val,
                            Op::Div => lhs_val / rhs_val,
                            Op::Mod => lhs_val % rhs_val,
                            _ => panic!(
                                "Unsupported operation for constant folding: {:?}",
                                bin_op.op
                            ),
                        };
                        Box::new(Literal::Int(result))
                    }
                    (Literal::Float(lhs_val), Literal::Float(rhs_val)) => {
                        let result = match bin_op.op {
                            Op::Add => lhs_val + rhs_val,
                            Op::Sub => lhs_val - rhs_val,
                            Op::Mul => lhs_val * rhs_val,
                            Op::Div => lhs_val / rhs_val,
                            _ => panic!(
                                "Unsupported operation for constant folding: {:?}",
                                bin_op.op
                            ),
                        };
                        Box::new(Literal::Float(result))
                    }
                    (Literal::Float(lhs_val), Literal::Int(rhs_val)) => {
                        let result = match bin_op.op {
                            Op::Add => lhs_val + rhs_val as f32,
                            Op::Sub => lhs_val - rhs_val as f32,
                            Op::Mul => lhs_val * rhs_val as f32,
                            Op::Div => lhs_val / rhs_val as f32,
                            _ => panic!(
                                "Unsupported operation for constant folding: {:?}",
                                bin_op.op
                            ),
                        };
                        Box::new(Literal::Float(result))
                    }
                    (Literal::Int(lhs_val), Literal::Float(rhs_val)) => {
                        let result = match bin_op.op {
                            Op::Add => lhs_val as f32 + rhs_val,
                            Op::Sub => lhs_val as f32 - rhs_val,
                            Op::Mul => lhs_val as f32 * rhs_val,
                            Op::Div => lhs_val as f32 / rhs_val,
                            _ => panic!(
                                "Unsupported operation for constant folding: {:?}",
                                bin_op.op
                            ),
                        };
                        Box::new(Literal::Float(result))
                    }
                    _ => unreachable!("Unsupported literal types occur in constant folding"),
                }
            } else {
                panic!("Non-constant folding operation: {:?}", bin_op.op);
            }
        } else if is::<UnaryOp>(&*node) {
            let un_op = cast_deref::<UnaryOp>(node).unwrap();
            let operand = self.fold(un_op.operand);

            if is::<Literal>(&*operand) {
                let lit = cast::<Literal>(&*operand).unwrap();
                match lit {
                    Literal::Int(val) => {
                        let result = match un_op.op {
                            Op::Plus => *val,
                            Op::Minus => -val,
                            _ => panic!(
                                "Unsupported unary operation for constant folding: {:?}",
                                un_op.op
                            ),
                        };
                        Box::new(Literal::Int(result))
                    }
                    Literal::Float(val) => {
                        let result = match un_op.op {
                            Op::Plus => *val,
                            Op::Minus => -val,
                            _ => panic!(
                                "Unsupported unary operation for constant folding: {:?}",
                                un_op.op
                            ),
                        };
                        Box::new(Literal::Float(result))
                    }
                    Literal::String(_) => {
                        unreachable!(
                            "Unsupported unary operation for constant folding on String: {:?}",
                            un_op.op
                        );
                    }
                }
            } else {
                panic!("Non-constant folding unary operation: {:?}", un_op.op);
            }
        } else if is::<Literal>(&*node) {
            let lit_node = cast_deref::<Literal>(node).unwrap();
            match *lit_node {
                Literal::Int(val) => Box::new(Literal::Int(val)),
                Literal::Float(val) => Box::new(Literal::Float(val)),
                Literal::String(ref val) => {
                    unreachable!("String literal folding is not supported yet: {}", val)
                }
            }
        } else if is::<VarAccess>(&*node) {
            let var_access = cast_mut::<VarAccess>(&mut *node).unwrap();
            if let Some(const_val) = self.syms.get(&var_access.name) {
                if is::<Literal>(&**const_val) {
                    let lit = cast::<Literal>(&**const_val).unwrap();
                    match *lit {
                        Literal::Int(val) => return Box::new(Literal::Int(val)),
                        Literal::Float(val) => return Box::new(Literal::Float(val)),
                        Literal::String(_) => {
                            unreachable!(
                                "String literal folding is not supported yet: {}",
                                var_access.name
                            );
                        }
                    }
                    // only supports literal folding
                } else {
                    panic!(
                        "Variable {} is not a constant literal for folding",
                        var_access.name
                    );
                }
            }
            panic!("Undefined variable {} for folding", var_access.name);
        } else if is::<ArrayAccess>(&*node) {
            let array_access = cast_mut::<ArrayAccess>(&mut node).unwrap();
            if let Some(array_val) = self.syms.get(&array_access.name) {
                if is::<ConstArray>(&**array_val) {
                    let const_array = cast::<ConstArray>(&**array_val).unwrap();
                    // calculate the flat index
                    let mut flat_index: usize = 0;
                    let mut stride: usize = 1;

                    // only supports full constant indices for folding
                    if array_access.indices.len()
                        != match &const_array.typ {
                            Type::Array { dims, .. } => dims.len(),
                            _ => panic!("ArrayAccess type is not Array"),
                        }
                    {
                        panic!(
                            "Array index dimension mismatch for folding: expected {}, found {}",
                            match &const_array.typ {
                                Type::Array { dims, .. } => dims.len(),
                                _ => panic!("ArrayAccess type is not Array"),
                            },
                            array_access.indices.len()
                        );
                    }
                    for index_node in array_access.indices.iter().rev() {
                        if is::<Literal>(&**index_node) {
                            let lit = cast::<Literal>(&**index_node).unwrap();
                            match *lit {
                                Literal::Int(idx) => {
                                    flat_index += (idx as usize) * stride;
                                    // calculate stride
                                    if let Type::Array { dims, .. } = &const_array.typ {
                                        stride *= *dims.last().unwrap() as usize;
                                    } else {
                                        panic!("ArrayAccess type is not Array");
                                    }
                                }
                                Literal::Float(idx) => {
                                    panic!(
                                        "Array index must be integer literal, found float: {}",
                                        idx
                                    );
                                }
                                Literal::String(_) => {
                                    panic!("Array index must be integer literal, found string");
                                }
                            }
                        } else {
                            panic!("Array index must be a constant literal for folding");
                        }
                    }
                    if let Some(init_values) = &const_array.init_values {
                        match init_values.get(flat_index) {
                            Some(val) => return val.clone(),
                            None => panic!(
                                "Array index out of bounds for folding: index {}, size {}",
                                flat_index,
                                init_values.len()
                            ),
                        }
                    } else {
                        // Else return 0
                        return Box::new(Literal::Int(0));
                    }
                } else {
                    panic!("ArrayAccess value is not ConstArray for folding");
                }
            }
            panic!("Undefined array {} for folding", array_access.name);
        } else {
            node
        }
    }

    // 1. Unfold the RawDecls into separate declarations.
    // 2. Flatten the array.
    pub fn canonicalize(&mut self, node: RawDecl) -> Vec<Box<dyn Node>> {
        let aggr_typ = node.typ.clone();
        let mut new_nodes: Vec<Box<dyn Node>> = vec![];

        for raw_decl in node.raw_decls.into_iter() {
            if raw_decl.const_exps.is_empty() {
                // Dispatch constant and non-constant here.
                let mut var_decl = Box::new(VarDecl {
                    name: raw_decl.ident,
                    // this will be overwritten later.
                    is_global: self.is_global(),
                    typ: aggr_typ.clone(),
                    mutable: node.mutable,
                    init_value: raw_decl.init_val,
                });
                // add to symbol table if it's constant
                var_decl.init_value = if !node.mutable {
                    if let Some(init_val) = var_decl.init_value {
                        let folded_init_val = cast_deref::<Literal>(self.fold(init_val)).unwrap();
                        self.syms
                            .insert(var_decl.name.clone(), folded_init_val.clone());
                        Some(folded_init_val)
                    } else {
                        panic!(
                            "Const variable {} must have an initial value",
                            var_decl.name
                        );
                    }
                } else {
                    var_decl.init_value
                };
                new_nodes.push(var_decl);
            } else {
                // fold the dimensions
                let dims: Vec<u32> = raw_decl
                    .const_exps
                    .into_iter()
                    // remember to fold it first.
                    .map(|exp_node| self.fold(exp_node))
                    .map(|exp_node| {
                        if is::<Literal>(&*exp_node) {
                            let lit = cast_deref::<Literal>(exp_node).unwrap();
                            if let Literal::Int(int_node) = *lit {
                                int_node as u32
                            } else {
                                panic!("Array size must be a constant integer: {:?}", lit);
                            }
                        } else {
                            panic!("Array size must be a constant literal or const variable");
                        }
                    })
                    .collect();
                // Flatten & Dispatch
                if node.mutable {
                    new_nodes.push(Box::new(VarArray {
                        name: raw_decl.ident,
                        is_global: self.is_global(),
                        typ: Type::Array {
                            base: Box::new(aggr_typ.clone()),
                            dims: dims.clone(),
                        },
                        // None: zeroinitializer
                        init_values: if let Some(init_val) = raw_decl.init_val {
                            crate::debug::info!("Flattening array: {:?}", &*init_val);
                            flatten(aggr_typ.clone(), dims, init_val)
                        } else {
                            None
                        },
                    }));
                } else {
                    // fold the initial values
                    let init_val = self.fold(raw_decl.init_val.expect(
                        // Validate the existence of initial value for constant array here.
                        // In the future, ConstArray.init_values == None represents zeroinitializer.
                        "ConstArray should have an initial value for constant folding!",
                    ));
                    let const_array = Box::new(ConstArray {
                        name: raw_decl.ident,
                        typ: Type::Array {
                            base: Box::new(aggr_typ.clone()),
                            dims: dims.clone(),
                        },
                        init_values: flatten(aggr_typ.clone(), dims.clone(), init_val),
                    });
                    // add to symbol table
                    self.syms
                        .insert(const_array.name.clone(), const_array.clone());
                    new_nodes.push(const_array);
                }
            }
        }
        new_nodes
    }
}

fn flatten(base_typ: Type, indices: Vec<u32>, node: Box<dyn Node>) -> Option<Vec<Box<dyn Node>>> {
    if !is::<ArrayInitVal>(&*node) {
        panic!("flatten can only process ArrayInitVal nodes");
    }
    let new_vals: RefCell<Vec<Box<dyn Node>>> = RefCell::new(vec![]);
    let mut has_non_zero = RefCell::new(false);

    {
        // flatten origin array
        let rec = fix(|f, params: (Box<dyn Node>, u32)| -> u32 {
            let (val, depth) = params;
            let mut filled_size: u32 = 0;

            // find minimal depth of current array.
            if is::<ArrayInitVal>(&*val) {
                info!("Catch ArrayInitVal at depth {}", depth);
                if new_vals.borrow().len() as u32 % indices.last().unwrap() != 0 {
                    panic!("Array has insufficient initializers");
                }

                let mut acc = 1;
                let mut idx = indices.len();
                for index in indices.iter().skip(depth as usize).rev() {
                    acc *= *index as usize;
                    if new_vals.borrow().len() % acc == 0 {
                        idx -= 1;
                    }
                }

                let array_init_val = *cast_deref::<ArrayInitVal>(val).unwrap();
                let vals = array_init_val.init_vals;
                let sub_filled_size = vals.into_iter().fold(filled_size, |filled_size, val| {
                    filled_size + f((val, depth + 1))
                });

                filled_size += sub_filled_size;

                let to_be_filled =
                    indices[idx..indices.len()].iter().product::<u32>() - filled_size;

                // fill 0
                (0..to_be_filled).for_each(|_| {
                    new_vals.borrow_mut().push(match base_typ.clone() {
                        Type::Int => Box::new(Literal::Int(0)),
                        Type::Float => Box::new(Literal::Float(0.0)),
                        _ => unreachable!(
                            "Only Int and Float types are supported in array initialization"
                        ),
                    });
                });

                filled_size += to_be_filled;
            } else {
                if let Some(val) = cast::<Literal>(&*val) {
                    match val {
                        Literal::Int(val) => {
                            if *val != 0 {
                                *has_non_zero.borrow_mut() = true;
                            }
                        }
                        Literal::Float(val) => {
                            if *val != 0.0 {
                                *has_non_zero.borrow_mut() = true;
                            }
                        }
                        _ => unreachable!(
                            "Only Int and Float literals are supported in array initialization"
                        ),
                    }
                }
                new_vals.borrow_mut().push(val);
                filled_size += 1;
            }

            filled_size
        });

        info!("\nOrigial ArrayInitVal: {:?}", &*node);
        rec((node, 0));
    }

    let expected_size = indices.iter().fold(1, |acc, index| acc * (*index as usize));
    if new_vals.borrow().len() != expected_size {
        error!(
            "Array has insufficient initializers: expected {}, found {}. \nFlattened values: {:?}",
            expected_size,
            new_vals.borrow().len(),
            new_vals.borrow()
        );
    }

    info!("Successfully flattened array: {:?}", new_vals.borrow());
    if !*has_non_zero.borrow() {
        None
    } else {
        Some(new_vals.into_inner())
    }
}
