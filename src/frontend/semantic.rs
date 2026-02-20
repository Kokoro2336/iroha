/**
 * Semantic analysis.
 * Performs type inference, add implicit cast and checks for semantic errors.
 */
use crate::base::Type;
use crate::base::SYSY_LIB;
use crate::base::{Pass, SymbolTable};
use crate::frontend::ast::*;
use crate::utils::arena::Arena;

use regex::Regex;
use std::collections::HashMap;

pub struct Semantic {
    pub ast: AST,
    funcs: HashMap<String, Type>,
    syms: SymbolTable<String, Type>,
    current_func: Option<String>,
}

impl Semantic {
    pub fn new(ast: AST) -> Self {
        Self {
            syms: SymbolTable::new(),
            funcs: HashMap::new(),
            current_func: None,
            ast,
        }
    }

    pub fn analyze(&mut self, node_id: NodeId) -> Result<Type, String> {
        let node_type = self.ast.get_node_type(node_id)?;
        match node_type {
            NodeType::BinaryOp => {
                crate::debug::info!("Semantic analyzing BinaryOp node: {:?}", &self.ast[node_id]);
                let op_kind = match &self.ast[node_id] {
                    Node::BinaryOp { op, .. } => op.clone(),
                    _ => unreachable!(),
                };

                // Flatten long chain expression into separate operations.
                let mut op_list: Vec<NodeId> = vec![];
                let origin = op_kind.clone();
                let mut cur = node_id;
                // Collect the operations with same kind.
                while let Node::BinaryOp { lhs, op, .. } = &self.ast[cur] {
                    if *op == origin {
                        op_list.push(cur);
                        // Since SysY's operator are all left-associative, the tree recurse on the left side of the tree.
                        cur = *lhs;
                    } else {
                        break;
                    }
                }

                fn infer(
                    ast: &mut AST,
                    lhs_id: &mut NodeId,
                    rhs_id: &mut NodeId,
                    lhs_type: Type,
                    rhs_type: Type,
                    op_kind: Op,
                ) -> Result<Type, String> {
                    if op_kind == Op::Mod
                        && (!matches!(lhs_type, Type::Int) || !matches!(rhs_type, Type::Int))
                    {
                        return Err("Modulo operator % only supports Int type".to_string());
                    }

                    if matches!(op_kind, Op::And | Op::Or) {
                        if matches!(lhs_type, Type::Float) {
                            let zero_id = ast.alloc(Node::Literal(Literal::Float(0.0)));
                            *lhs_id = ast.alloc(Node::BinaryOp {
                                typ: Type::Int,
                                lhs: *lhs_id,
                                op: Op::Ne,
                                rhs: zero_id,
                            });
                        }
                        if matches!(rhs_type, Type::Float) {
                            let zero_id = ast.alloc(Node::Literal(Literal::Float(0.0)));
                            *rhs_id = ast.alloc(Node::BinaryOp {
                                typ: Type::Int,
                                lhs: *rhs_id,
                                op: Op::Ne,
                                rhs: zero_id,
                            });
                        }
                    }

                    if matches!(lhs_type, Type::Int) && matches!(rhs_type, Type::Float) {
                        *lhs_id = ast.alloc(Node::UnaryOp {
                            typ: Type::Float,
                            op: Op::Cast(Type::Int, Type::Float),
                            operand: *lhs_id,
                        });
                    } else if matches!(lhs_type, Type::Float) && matches!(rhs_type, Type::Int) {
                        *rhs_id = ast.alloc(Node::UnaryOp {
                            typ: Type::Float,
                            op: Op::Cast(Type::Int, Type::Float),
                            operand: *rhs_id,
                        });
                    }

                    let ret_typ = if op_kind.only_ret_int() {
                        Type::Int
                    } else if matches!(lhs_type, Type::Float) || matches!(rhs_type, Type::Float) {
                        Type::Float
                    } else {
                        Type::Int
                    };
                    Ok(ret_typ)
                }

                let mut res = Type::Void;
                for (idx, op_id) in op_list.into_iter().rev().enumerate() {
                    let (mut lhs_id, mut rhs_id, op_kind) = match &self.ast[op_id] {
                        Node::BinaryOp { lhs, rhs, op, .. } => (*lhs, *rhs, op.clone()),
                        _ => return Err(format!("Expected RVal node, got {:?}", &self.ast[op_id])),
                    };

                    let lhs_type = if idx == 0 {
                        // This first element's lhs is not original type, so we need to invoke analyze() for it.
                        self.analyze(lhs_id)?
                    } else {
                        // res is currently the type of the previous operation, which is the new lhs type for current operation.
                        res.clone()
                    };
                    let rhs_type = self.analyze(rhs_id)?;
                    let ret_typ = infer(
                        &mut self.ast,
                        &mut lhs_id,
                        &mut rhs_id,
                        lhs_type,
                        rhs_type,
                        op_kind,
                    )?;
                    if let Node::BinaryOp { typ, lhs, rhs, .. } = &mut self.ast[op_id] {
                        *typ = ret_typ.clone();
                        *lhs = lhs_id;
                        *rhs = rhs_id;
                    }
                    // The result type of current operation, which will be used as lhs type for the next operation in the chain.
                    res = ret_typ;
                }

                Ok(res)
            }
            NodeType::UnaryOp => {
                crate::debug::info!("Semantic analyzing UnaryOp node: {:?}", &self.ast[node_id]);
                let op_kind = match &self.ast[node_id] {
                    Node::UnaryOp { op, .. } => op.clone(),
                    _ => unreachable!(),
                };

                if matches!(op_kind, Op::Cast(_, _)) {
                    panic!("Cast op is impossible to occur before semantic analysis!");
                }

                let mut op_list: Vec<NodeId> = vec![];
                let origin = op_kind.clone();
                let mut cur = node_id;
                while let Node::UnaryOp { op, operand, .. } = &self.ast[cur] {
                    if *op == origin {
                        op_list.push(cur);
                        cur = *operand;
                    } else {
                        break;
                    }
                }

                match op_kind {
                    Op::Plus => {
                        // If the operand is Plus, we eliminate the unary plus operator.
                        let last_id = op_list.last().copied().unwrap();
                        let operand_id = match &self.ast[last_id] {
                            Node::UnaryOp { operand, .. } => *operand,
                            _ => {
                                return Err(format!(
                                    "Expected UnaryOp node, got {:?}",
                                    &self.ast[last_id]
                                ))
                            }
                        };
                        let operand_type = self.analyze(operand_id)?;
                        // Replace the root unary node with its operand node, in place.
                        let operand = self.ast[operand_id].clone();
                        self.ast.replace(node_id, operand)?;
                        // Remove redundant unary chain nodes and duplicated operand node.
                        for id in op_list.into_iter().filter(|id| *id != node_id) {
                            self.ast.remove(id)?;
                        }
                        self.ast.remove(operand_id)?;
                        Ok(operand_type)
                    }
                    Op::Minus | Op::Not => {
                        // Eliminate the unary/minus operator.
                        let last_id = op_list.last().copied().unwrap();
                        let operand_id = match &self.ast[last_id] {
                            Node::UnaryOp { operand, .. } => *operand,
                            _ => {
                                return Err(format!(
                                    "Expected UnaryOp node, got {:?}",
                                    &self.ast[last_id]
                                ))
                            }
                        };
                        let operand_type = self.analyze(operand_id)?;

                        let res_id = if op_list.len() % 2 == 0 {
                            // Even count: unary chain cancels out.
                            let operand = self.ast[operand_id].clone();
                            self.ast.replace(node_id, operand)?;
                            // Remove redundant unary chain nodes and duplicated operand node.
                            for id in op_list.into_iter().filter(|id| *id != node_id) {
                                self.ast.remove(id)?;
                            }
                            self.ast.remove(operand_id)?;
                            return Ok(operand_type);
                        } else {
                            // Odd count: keep one operator at the root and point directly to base operand.
                            if let Node::UnaryOp { operand, .. } = &mut self.ast[node_id] {
                                *operand = operand_id;
                            }
                            // Remove redundant unary chain nodes, keep root and base operand.
                            for id in op_list.iter().copied().filter(|id| *id != node_id) {
                                self.ast.remove(id)?;
                            }
                            operand_id
                        };

                        if op_kind == Op::Not && matches!(operand_type, Type::Float) {
                            let zero_id = self.ast.alloc(Node::Literal(Literal::Float(0.0)));
                            let new_res_id = self.ast.alloc(Node::BinaryOp {
                                typ: Type::Int,
                                op: Op::Ne,
                                lhs: res_id,
                                rhs: zero_id,
                            });
                            if let Node::UnaryOp { typ, operand, .. } = &mut self.ast[node_id] {
                                *typ = Type::Int;
                                *operand = new_res_id;
                            }
                            return Ok(Type::Int);
                        }
                        match &mut self.ast[node_id] {
                            Node::UnaryOp { typ, operand, .. } => {
                                *typ = operand_type.clone();
                                *operand = res_id;
                                Ok(operand_type)
                            }
                            _ => Err(format!(
                                "Expected UnaryOp node, got {:?}",
                                &self.ast[node_id]
                            )),
                        }
                    }
                    _ => Err(format!("Unsupported unary operator: {:?}", op_kind)),
                }
            }
            NodeType::Literal => match &self.ast[node_id] {
                Node::Literal(Literal::Int(_)) => Ok(Type::Int),
                Node::Literal(Literal::Float(_)) => Ok(Type::Float),
                Node::Literal(Literal::String(_)) => Ok(Type::Pointer {
                    base: Box::new(Type::Char),
                }),
                _ => unreachable!(),
            },
            NodeType::VarAccess => {
                let name = match &self.ast[node_id] {
                    Node::VarAccess { name, .. } => name.clone(),
                    _ => unreachable!(),
                };

                if let Some(var_type) = self.syms.get(&name) {
                    if let Node::VarAccess { typ, .. } = &mut self.ast[node_id] {
                        *typ = var_type.clone();
                    }
                    Ok(var_type.clone())
                } else {
                    Err(format!("Undefined variable: {}", name))
                }
            }
            NodeType::Call => {
                let (func_name, mut args_ids) = match &self.ast[node_id] {
                    Node::Call {
                        func_name, args, ..
                    } => (func_name.clone(), args.clone()),
                    _ => unreachable!(),
                };

                let (fn_params, return_typ) = if let Some(func_typ) = self.funcs.get(&func_name) {
                    if let Type::Function {
                        return_type,
                        param_types,
                    } = func_typ
                    {
                        (param_types.clone(), *return_type.clone())
                    } else {
                        return Err(format!("{} is not a function", func_name));
                    }
                } else {
                    return Err(format!("Undefined FnDecl: {}", func_name));
                };

                if func_name != "putf" {
                    if fn_params.len() != args_ids.len() {
                        return Err(format!(
                            "Function {} expects {} arguments, got {}",
                            func_name,
                            fn_params.len(),
                            args_ids.len()
                        ));
                    }

                    for (i, arg_id) in args_ids.iter_mut().enumerate() {
                        let arg_type = self.analyze(*arg_id)?;
                        let param_type = &fn_params[i];
                        if matches!(arg_type, Type::Float) && matches!(*param_type, Type::Int)
                            || matches!(arg_type, Type::Int) && matches!(*param_type, Type::Float)
                        {
                            *arg_id = self.ast.alloc(Node::UnaryOp {
                                typ: param_type.clone(),
                                op: Op::Cast(arg_type, param_type.clone()),
                                operand: *arg_id,
                            });
                        } else if arg_type != *param_type {
                            return Err(format!(
                                "Argument type mismatch in function {}: expected {:?}, got {:?}",
                                func_name, param_type, arg_type
                            ));
                        }
                    }
                } else {
                    if args_ids.is_empty() {
                        return Err("putf expects at least one argument".to_string());
                    }
                    let fmt_str = if let Node::Literal(Literal::String(s)) = &self.ast[args_ids[0]]
                    {
                        s.clone()
                    } else {
                        return Err(
                            "The first argument of putf must be a string literal".to_string()
                        );
                    };

                    let re = Regex::new(r"%.").unwrap();
                    let mut placeholder_types = Vec::new();
                    for cap in re.captures_iter(&fmt_str) {
                        match &cap[0] {
                            "%d" | "%c" => placeholder_types.push(Type::Int),
                            "%f" => placeholder_types.push(Type::Float),
                            s => return Err(format!("Unsupported format specifier: {}", s)),
                        }
                    }

                    if args_ids.len() - 1 != placeholder_types.len() {
                        return Err(format!(
                            "putf expects {} arguments, got {}",
                            placeholder_types.len(),
                            args_ids.len() - 1
                        ));
                    }

                    for (i, arg_id) in args_ids.iter_mut().skip(1).enumerate() {
                        let arg_type = self.analyze(*arg_id)?;
                        let param_type = &placeholder_types[i];
                        if (matches!(arg_type, Type::Float) && matches!(*param_type, Type::Int))
                            || (matches!(arg_type, Type::Int) && matches!(*param_type, Type::Float))
                        {
                            *arg_id = self.ast.alloc(Node::UnaryOp {
                                typ: param_type.clone(),
                                op: Op::Cast(arg_type, param_type.clone()),
                                operand: *arg_id,
                            });
                        } else if arg_type != *param_type {
                            return Err(format!(
                                "Argument type mismatch in putf: expected {:?}, got {:?}",
                                param_type, arg_type
                            ));
                        }
                    }
                }

                if let Node::Call { typ, args, .. } = &mut self.ast[node_id] {
                    *typ = return_typ.clone();
                    *args = args_ids;
                }
                Ok(return_typ)
            }
            NodeType::ArrayAccess => {
                let (name, indices_ids) = match &self.ast[node_id] {
                    Node::ArrayAccess { name, indices, .. } => (name.clone(), indices.clone()),
                    _ => unreachable!(),
                };
                let array_type = match self.syms.get(&name) {
                    Some(typ) => typ.clone(),
                    None => return Err(format!("Undefined variable: {}", name)),
                };

                for index in &indices_ids {
                    self.analyze(*index)?;
                }

                let inferred = if let Type::Array { base, dims } = array_type {
                    let new_dims = if indices_ids.len() > dims.len() {
                        return Err(format!(
                            "Too many indices for array access! Expected at most {}, got {}",
                            dims.len(),
                            indices_ids.len()
                        ));
                    } else {
                        dims[indices_ids.len()..].to_vec()
                    };
                    if new_dims.is_empty() {
                        base.as_ref().clone()
                    } else {
                        decay(Type::Array {
                            base: base.clone(),
                            dims: new_dims,
                        })?
                    }
                } else if let Type::Pointer { .. } = array_type {
                    let raised = raise(array_type)?;
                    if let Type::Array { base, dims } = raised {
                        let new_dims = if indices_ids.len() > dims.len() {
                            return Err(format!(
                                "Too many indices for array access! Expected at most {}, got {}",
                                dims.len(),
                                indices_ids.len()
                            ));
                        } else {
                            dims[indices_ids.len()..].to_vec()
                        };
                        if new_dims.is_empty() {
                            base.as_ref().clone()
                        } else {
                            decay(Type::Array {
                                base: base.clone(),
                                dims: new_dims,
                            })?
                        }
                    } else {
                        unreachable!("Raised pointer type is not array type!")
                    }
                } else {
                    return Err(format!(
                        "Variable {} is not an array, cannot access with indices. Got type {:?}",
                        name, array_type
                    ));
                };

                if let Node::ArrayAccess { typ, .. } = &mut self.ast[node_id] {
                    *typ = inferred.clone();
                }
                Ok(inferred)
            }
            NodeType::FnDecl => {
                let (name, params, typ, body) = match &self.ast[node_id] {
                    Node::FnDecl {
                        name,
                        params,
                        typ,
                        body,
                    } => (name.clone(), params.clone(), typ.clone(), *body),
                    _ => unreachable!(),
                };
                self.funcs.insert(name.clone(), typ);
                self.syms.enter_scope();
                for param in &params {
                    self.syms.insert(param.0.clone(), param.1.clone());
                }
                self.current_func = Some(name);
                self.analyze(body)?;
                self.syms.exit_scope();
                Ok(Type::Void)
            }
            NodeType::VarDecl => {
                let (name, decl_type, mut init_value) = match &self.ast[node_id] {
                    Node::VarDecl {
                        name,
                        typ,
                        init_value,
                        ..
                    } => (name.clone(), typ.clone(), *init_value),
                    _ => unreachable!(),
                };
                self.syms.insert(name, decl_type.clone());
                if let Some(init_id) = init_value {
                    let val_typ = self.analyze(init_id)?;
                    if matches!(val_typ, Type::Float) && matches!(decl_type, Type::Int)
                        || matches!(val_typ, Type::Int) && matches!(decl_type, Type::Float)
                    {
                        init_value = Some(self.ast.alloc(Node::UnaryOp {
                            typ: decl_type.clone(),
                            op: Op::Cast(val_typ, decl_type.clone()),
                            operand: init_id,
                        }));
                    } else if val_typ != decl_type {
                        return Err(format!(
                            "Variable type mismatch: expected {:?}, got {:?}",
                            decl_type, val_typ
                        ));
                    }
                }
                if let Node::VarDecl { init_value: iv, .. } = &mut self.ast[node_id] {
                    *iv = init_value;
                }
                Ok(Type::Void)
            }
            NodeType::ConstArray => {
                let (name, array_type, init_values) = match &self.ast[node_id] {
                    Node::ConstArray {
                        name,
                        typ,
                        init_values,
                    } => (name.clone(), typ.clone(), init_values.clone()),
                    _ => unreachable!(),
                };
                self.syms.insert(name, decay(array_type.clone())?);
                let base = match &array_type {
                    Type::Array { base, .. } => base.as_ref().clone(),
                    _ => panic!("ConstArray must have array type!"),
                };

                if let Some(init_ids) = init_values {
                    for init_id in init_ids {
                        let val_type = self.analyze(init_id)?;
                        if val_type != base {
                            match &mut self.ast[init_id] {
                                Node::Literal(literal) => match val_type {
                                    Type::Int => {
                                        *literal = Literal::Float(literal.get_int() as f32)
                                    }
                                    Type::Float => *literal = Literal::Float(literal.get_float()),
                                    _ => {
                                        return Err(format!(
                                            "ConstArray can only be initialized with Int or Float literals: {:?}",
                                            val_type
                                        ));
                                    }
                                },
                                _ => {
                                    return Err("ConstArray initializer must be literal".to_string())
                                }
                            }
                        }
                    }
                }
                Ok(Type::Void)
            }
            NodeType::VarArray => {
                let (name, array_type, mut init_values) = match &self.ast[node_id] {
                    Node::VarArray {
                        name,
                        typ,
                        init_values,
                        ..
                    } => (name.clone(), typ.clone(), init_values.clone()),
                    _ => unreachable!(),
                };
                self.syms.insert(name, decay(array_type.clone())?);

                if let Some(init_ids) = &mut init_values {
                    let base_typ = match &array_type {
                        Type::Array { base, .. } => base.as_ref().clone(),
                        _ => panic!("VarArray must have array type!"),
                    };

                    for init_id in init_ids.iter_mut() {
                        let val_typ = self.analyze(*init_id)?;
                        if matches!(val_typ, Type::Float) && matches!(base_typ, Type::Int)
                            || matches!(val_typ, Type::Int) && matches!(base_typ, Type::Float)
                        {
                            *init_id = self.ast.alloc(Node::UnaryOp {
                                typ: base_typ.clone(),
                                op: Op::Cast(val_typ, base_typ.clone()),
                                operand: *init_id,
                            });
                        } else if val_typ != base_typ {
                            return Err(format!(
                                "Array variable type mismatch: expected {:?}, got {:?}",
                                base_typ, val_typ
                            ));
                        }
                    }
                }

                if let Node::VarArray {
                    init_values: iv, ..
                } = &mut self.ast[node_id]
                {
                    *iv = init_values;
                }
                Ok(Type::Void)
            }
            NodeType::Block => {
                let statements = match &self.ast[node_id] {
                    Node::Block { statements } => statements.clone(),
                    _ => unreachable!(),
                };
                self.syms.enter_scope();
                for stmt in statements {
                    self.analyze(stmt)?;
                }
                self.syms.exit_scope();
                Ok(Type::Void)
            }
            NodeType::If => {
                let (mut condition, then_block, else_block) = match &self.ast[node_id] {
                    Node::If {
                        condition,
                        then_block,
                        else_block,
                    } => (*condition, *then_block, *else_block),
                    _ => unreachable!(),
                };
                let cond_type = self.analyze(condition)?;
                if matches!(cond_type, Type::Float) {
                    let zero_id = self.ast.alloc(Node::Literal(Literal::Float(0.0)));
                    condition = self.ast.alloc(Node::BinaryOp {
                        typ: Type::Int,
                        lhs: condition,
                        op: Op::Ne,
                        rhs: zero_id,
                    });
                }
                self.analyze(then_block)?;
                if let Some(else_id) = else_block {
                    self.analyze(else_id)?;
                }
                if let Node::If { condition: c, .. } = &mut self.ast[node_id] {
                    *c = condition;
                }
                Ok(Type::Void)
            }
            NodeType::While => {
                let (mut condition, body) = match &self.ast[node_id] {
                    Node::While { condition, body } => (*condition, *body),
                    _ => unreachable!(),
                };
                let cond_type = self.analyze(condition)?;
                if matches!(cond_type, Type::Float) {
                    let zero_id = self.ast.alloc(Node::Literal(Literal::Float(0.0)));
                    condition = self.ast.alloc(Node::BinaryOp {
                        typ: Type::Int,
                        lhs: condition,
                        op: Op::Ne,
                        rhs: zero_id,
                    });
                }
                self.analyze(body)?;
                if let Node::While { condition: c, .. } = &mut self.ast[node_id] {
                    *c = condition;
                }
                Ok(Type::Void)
            }
            NodeType::Return => {
                let mut expr = match &self.ast[node_id] {
                    Node::Return(expr) => *expr,
                    _ => unreachable!(),
                };

                if let Some(id) = expr {
                    let ret_typ = self.analyze(id)?;
                    let func_typ = self
                        .funcs
                        .get(self.current_func.as_ref().unwrap())
                        .unwrap()
                        .clone();
                    let func_ret_typ = match func_typ {
                        Type::Function { return_type, .. } => *return_type,
                        _ => {
                            return Err(format!(
                                "Current function {} does not have a valid function type!",
                                self.current_func.as_ref().unwrap()
                            ));
                        }
                    };

                    if (matches!(func_ret_typ, Type::Float) && matches!(ret_typ, Type::Int))
                        || (matches!(func_ret_typ, Type::Int) && matches!(ret_typ, Type::Float))
                    {
                        expr = Some(self.ast.alloc(Node::UnaryOp {
                            typ: func_ret_typ.clone(),
                            op: Op::Cast(ret_typ, func_ret_typ.clone()),
                            operand: id,
                        }));
                    } else if ret_typ != func_ret_typ {
                        return Err(format!(
                            "Return type mismatch in function {}: expected {:?}, got {:?}",
                            self.current_func.as_ref().unwrap(),
                            func_ret_typ,
                            ret_typ
                        ));
                    }
                }

                if let Node::Return(ret) = &mut self.ast[node_id] {
                    *ret = expr;
                }
                Ok(Type::Void)
            }
            NodeType::Assign => {
                let (lhs_id, mut rhs_id) = match &self.ast[node_id] {
                    Node::Assign { lhs, rhs } => (*lhs, *rhs),
                    _ => unreachable!(),
                };
                let lhs_type = self.analyze(lhs_id)?;
                let rhs_type = self.analyze(rhs_id)?;
                if (matches!(lhs_type, Type::Float) && matches!(rhs_type, Type::Int))
                    || (matches!(lhs_type, Type::Int) && matches!(rhs_type, Type::Float))
                {
                    rhs_id = self.ast.alloc(Node::UnaryOp {
                        typ: lhs_type.clone(),
                        op: Op::Cast(rhs_type, lhs_type),
                        operand: rhs_id,
                    });
                } else if lhs_type != rhs_type {
                    return Err(format!(
                        "Assignment type mismatch: expected {:?}, got {:?}",
                        lhs_type, rhs_type
                    ));
                }

                if let Node::Assign { rhs, .. } = &mut self.ast[node_id] {
                    *rhs = rhs_id;
                }
                Ok(Type::Void)
            }
            _ => Ok(Type::Void),
        }
    }
}

impl Pass<AST> for Semantic {
    fn run(&mut self) -> Result<AST, String> {
        self.syms.enter_scope();
        SYSY_LIB.with(|lib| {
            for (name, typ) in lib.iter() {
                self.funcs.insert(name.to_string(), typ.clone());
            }
        });

        let entry = self
            .ast
            .entry
            .ok_or("Semantic: AST entry is missing".to_string())?;
        self.analyze(entry)?;

        self.syms.exit_scope();
        Ok(std::mem::replace(&mut self.ast, AST::new()))
    }
}

// Array -> Pointer
pub fn decay(typ: Type) -> Result<Type, String> {
    match typ {
        Type::Array { base, dims } => {
            if dims.is_empty() {
                return Err("Cannot decay array with zero dimensions!".to_string());
            }
            if dims.len() == 1 {
                Ok(Type::Pointer { base })
            } else {
                Ok(Type::Pointer {
                    base: Box::new(Type::Array {
                        base,
                        dims: dims[1..].to_vec(),
                    }),
                })
            }
        }
        Type::Pointer { .. } => Ok(typ),
        _ => Err(format!("Cannot decay non-array type: {:?}", typ)),
    }
}

pub fn raise(typ: Type) -> Result<Type, String> {
    match typ {
        Type::Pointer { base } => match *base {
            Type::Array {
                base: array_base,
                dims,
            } => {
                if dims.is_empty() {
                    return Err("Cannot raise pointer to array with zero dimensions!".to_string());
                } else {
                    Ok(Type::Array {
                        base: array_base,
                        dims: std::iter::once(1).chain(dims).collect(),
                    })
                }
            }
            _ => Ok(Type::Array {
                base,
                dims: vec![1],
            }),
        },
        _ => Err(format!("Cannot raise non-pointer type: {:?}", typ)),
    }
}
