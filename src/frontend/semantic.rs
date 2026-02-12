use crate::base::Type;
/**
 * Semantic analysis.
 * Performs type inference, add implicit cast and checks for semantic errors.
 */
use crate::base::{Pass, SymbolTable};
use crate::frontend::ast::*;
use crate::utils::{cast, cast_mut, is, replace, take};

use regex::Regex;

pub struct Semantic {
    pub node: Option<Box<dyn Node>>,
    syms: SymbolTable<String, Type>,
    // func_name: String, param_names: Vec<String>, param_added: bool
    current_func: Option<String>,
}

impl Semantic {
    pub fn new(node: Box<dyn Node>) -> Self {
        // Add SysY lib functions
        Self {
            syms: SymbolTable::new(),
            current_func: None,
            node: Some(node),
        }
    }

    pub fn analyze(&mut self, node: &mut Box<dyn Node>) -> Result<Type, String> {
        // Exps
        if is::<BinaryOp>(node) {
            let bin_op = cast_mut::<BinaryOp>(node).unwrap();
            let lhs_type = self.analyze(&mut bin_op.lhs)?;
            let rhs_type = self.analyze(&mut bin_op.rhs)?;

            // Modulo
            if bin_op.op == Op::Mod && (!matches!(lhs_type, Type::Int) || !matches!(rhs_type, Type::Int)) {
                return Err("Modulo operator % only supports Int type".to_string());
            }

            // And & Or
            if matches!(bin_op.op, Op::And | Op::Or) {
                if matches!(lhs_type, Type::Float) {
                    bin_op.lhs = Box::new(BinaryOp {
                        typ: Type::Int,
                        lhs: take(&mut bin_op.lhs),
                        op: Op::Ne,
                        rhs: Box::new(Literal::Float(0.0)),
                    });
                }

                if matches!(rhs_type, Type::Float) {
                    bin_op.rhs = Box::new(BinaryOp {
                        typ: Type::Int,
                        lhs: take(&mut bin_op.rhs),
                        op: Op::Ne,
                        rhs: Box::new(Literal::Float(0.0)),
                    });
                }
            }

            // Implicit cast
            if matches!(lhs_type, Type::Int) && matches!(rhs_type, Type::Float) {
                bin_op.lhs = Box::new(UnaryOp {
                    typ: Type::Float,
                    op: Op::Cast(Type::Int, Type::Float),
                    operand: take(&mut bin_op.lhs),
                });
            } else if matches!(lhs_type, Type::Float) && matches!(rhs_type, Type::Int) {
                bin_op.rhs = Box::new(UnaryOp {
                    typ: Type::Float,
                    op: Op::Cast(Type::Int, Type::Float),
                    operand: take(&mut bin_op.rhs),
                });
            }

            // return type
            // if the operation doesn't allow float return type, directly return Int
            if bin_op.op.only_ret_int() {
                bin_op.typ = Type::Int;
                Ok(Type::Int)
            } else if matches!(lhs_type, Type::Float) || matches!(rhs_type, Type::Float) {
                bin_op.typ = Type::Float;
                Ok(Type::Float)
            } else {
                bin_op.typ = Type::Int;
                Ok(Type::Int)
            }
        } else if is::<UnaryOp>(node) {
            let un_op = cast_mut::<UnaryOp>(node).unwrap();
            if matches!(un_op.op, Op::Cast(_, _)) {
                panic!("Cast op is impossible to occur before semantic analysis!");
            }
            let operand_type = self.analyze(&mut un_op.operand)?;

            // Insert Ne for float
            match un_op.op {
                Op::Plus => {
                    // remove the plus node
                    let operand = take(&mut un_op.operand);
                    replace(node, operand);
                    Ok(operand_type)
                }
                Op::Minus => {
                    // Minus always returns the same type as operand
                    Ok(operand_type)
                }
                Op::Not => {
                    // Insert Ne for float
                    if matches!(operand_type, Type::Float) {
                        un_op.operand = Box::new(BinaryOp {
                            typ: Type::Int,
                            lhs: take(&mut un_op.operand),
                            op: Op::Ne,
                            rhs: Box::new(Literal::Float(0.0)),
                        });
                    }
                    Ok(Type::Int)
                }
                _ => unreachable!("Unexpected unary op: {:?}", un_op),
            }
        } else if is::<Literal>(node) {
            let lit = cast_mut::<Literal>(node).unwrap();
            match *lit {
                Literal::Int(_) => Ok(Type::Int),
                Literal::Float(_) => Ok(Type::Float),
                Literal::String(_) => Ok(Type::Pointer {
                    base: Box::new(Type::Char),
                }),
            }
        } else if is::<VarAccess>(node) {
            let var_access = cast_mut::<VarAccess>(node).unwrap();
            if let Some(var_type) = self.syms.get(&var_access.name) {
                var_access.typ = var_type.clone();
                Ok(var_type.clone())
            } else {
                return Err(format!("Undefined variable: {}", var_access.name));
            }
        } else if is::<Call>(node) {
            let call = cast_mut::<Call>(node).unwrap();
            let (fn_params, return_typ) = if let Some(func_typ) = self.syms.get(&call.func_name) {
                match func_typ {
                    Type::Function {
                        return_type,
                        param_types,
                    } => (param_types.clone(), *return_type.clone()),
                    _ => return Err(format!("{} is not a function", call.func_name)),
                }
            } else {
                return Err(format!("Undefined FnDecl: {}", call.func_name));
            };

            // check argument types
            if call.func_name != "putf" {
                if fn_params.len() != call.args.len() {
                    return Err(format!(
                        "Function {} expects {} arguments, got {}",
                        call.func_name,
                        fn_params.len(),
                        call.args.len()
                    ));
                }
                for (i, arg) in call.args.iter_mut().enumerate() {
                    let arg_type = self.analyze(arg)?;
                    let param_type = &fn_params[i];
                    if (arg_type == Type::Void) ^ (param_type == &Type::Void) {
                        return Err(format!(
                            "Argument type mismatch in function {}: expected {:?}, got {:?}",
                            call.func_name, param_type, arg_type
                        ));
                    } else if arg_type != *param_type {
                        // insert implicit cast
                        *arg = Box::new(UnaryOp {
                            typ: param_type.clone(),
                            op: Op::Cast(arg_type, param_type.clone()),
                            operand: take(arg),
                        });
                    }
                }
            } else {
                if call.args.is_empty() {
                    return Err("putf expects at least one argument".to_string());
                }

                let fmt_str = if let Some(lit) = cast::<Literal>(&*call.args[0]) {
                    match lit {
                        Literal::String(s) => s.clone(),
                        _ => return Err("The first argument of putf must be a string literal".to_string()),
                    }
                } else {
                    return Err("The first argument of putf must be a string literal".to_string());
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

                if call.args.len() - 1 != placeholder_types.len() {
                    return Err(format!(
                        "putf expects {} arguments, got {}",
                        placeholder_types.len(),
                        call.args.len() - 1
                    ));
                }

                for (i, arg) in call.args.iter_mut().skip(1).enumerate() {
                    let arg_type = self.analyze(arg)?;
                    let param_type = &placeholder_types[i];
                    if arg_type != *param_type {
                        *arg = Box::new(UnaryOp {
                            typ: param_type.clone(),
                            op: Op::Cast(arg_type, param_type.clone()),
                            operand: take(arg),
                        });
                    }
                }
            }

            call.typ = return_typ.clone();
            Ok(return_typ)
        } else if is::<ArrayAccess>(node) {
            let array_access = cast_mut::<ArrayAccess>(node).unwrap();
            let array_type = self.syms.get(&array_access.name).ok_or_else(|| {
                format!("Undefined array variable: {}", array_access.name)
            })?;

            // infer the access's typ
            array_access.typ = if let Type::Array { base, dims } = array_type {
                let new_dims = dims.clone()[array_access.indices.len()..].to_vec();
                // if new_dims is empty, return base type; else decay it to pointer.
                if new_dims.is_empty() {
                    base.as_ref().clone()
                } else {
                    decay(Type::Array {
                        base: base.clone(),
                        dims: new_dims,
                    })?
                }
            } else {
                return Err(format!(
                    "Variable {} is not an array, cannot access with indices",
                    array_access.name
                ));
            };
            Ok(array_access.typ.clone())

        // Declarations
        } else if is::<FnDecl>(node) {
            let func = cast_mut::<FnDecl>(node).unwrap();
            self.syms
                .insert(func.name.clone(), func.typ.clone());
            // enter the scope created for function itself, which is 1 level higher than the function body scope
            self.syms.enter_scope();

            // insert parameters into symbol table
            for param in &func.params {
                self.syms.insert(param.0.clone(), param.1.clone());
            }
            // add current function info
            self.current_func = Some(func.name.clone());
            self.analyze(&mut func.body)?;

            self.syms.exit_scope();
            Ok(Type::Void)
        } else if is::<VarDecl>(node) {
            let var_decl = cast_mut::<VarDecl>(node).unwrap();
            self.syms
                .insert(var_decl.name.clone(), var_decl.typ.clone());
            if let Some(init_value) = &mut var_decl.init_value {
                let val_typ = self.analyze(init_value)?;
                // if val_typ does not match the decl's typ, insert implicit cast
                if val_typ != var_decl.typ {
                    var_decl.init_value = Some(Box::new(UnaryOp {
                        typ: var_decl.typ.clone(),
                        op: Op::Cast(val_typ, var_decl.typ.clone()),
                        operand: take(init_value),
                    }));
                }
            }
            Ok(Type::Void)
        } else if is::<ConstArray>(node) {
            let const_array = cast_mut::<ConstArray>(node).unwrap();
            self.syms
                .insert(const_array.name.clone(), const_array.typ.clone());
            let base = match &const_array.typ {
                Type::Array { base, .. } => base.as_ref().clone(),
                _ => panic!("ConstArray must have array type!"),
            };

            for init_val in &mut const_array.init_values {
                let val_type = self.analyze(init_val)?;
                // We don't insert cast node for ConstArray, we directly modify the init_val node.
                if val_type != base {
                    let literal = cast_mut::<Literal>(init_val).unwrap();
                    match val_type {
                        // if val_typ == Type::Int and val_typ != base, then base must be Float
                        Type::Int => {
                            *literal = Literal::Float(literal.get_int() as f32);
                        }
                        Type::Float => {
                            *literal = Literal::Float(literal.get_float());
                        }
                        _ => unreachable!(
                            "ConstArray can only be initialized with Int or Float literals: {:?}",
                            val_type
                        ),
                    }
                }
            }
            Ok(Type::Void)
        } else if is::<VarArray>(node) {
            let local_array = cast_mut::<VarArray>(node).unwrap();
            self.syms
                .insert(local_array.name.clone(), local_array.typ.clone());
            if let Some(init_values) = &mut local_array.init_values {
                for init_val in init_values {
                    let val_typ = self.analyze(init_val)?;
                    // since we don't know whether the init_values is float or int, we insert cast node here.
                    if val_typ != local_array.typ {
                        match val_typ {
                            Type::Int => {
                                *init_val = Box::new(UnaryOp {
                                    typ: local_array.typ.clone(),
                                    op: Op::Cast(Type::Int, local_array.typ.clone()),
                                    operand: take(init_val),
                                });
                            },
                            Type::Float => {
                                *init_val = Box::new(UnaryOp {
                                    typ: local_array.typ.clone(),
                                    op: Op::Cast(Type::Float, local_array.typ.clone()),
                                    operand: take(init_val),
                                });
                            },
                            _ => unreachable!(
                                "LocalArray can only be initialized with Int or Float literals: {:?}", val_typ
                            ),
                        }
                    }
                }
            }
            Ok(Type::Void)

        // Statements
        } else if is::<Block>(node) {
            let block = cast_mut::<Block>(node).unwrap();
            self.syms.enter_scope();
            for stmt in &mut block.statements {
                self.analyze(stmt)?;
            }
            self.syms.exit_scope();
            Ok(Type::Void)
        } else if is::<If>(node) {
            let if_stmt = cast_mut::<If>(node).unwrap();
            // Do implicit cast for cond if necessary.
            let cond_type = self.analyze(&mut if_stmt.condition)?;
            if matches!(cond_type, Type::Float) {
                if_stmt.condition = Box::new(BinaryOp {
                    typ: Type::Int,
                    lhs: take(&mut if_stmt.condition),
                    op: Op::Ne,
                    rhs: Box::new(Literal::Float(0.0)),
                });
            }

            self.analyze(&mut if_stmt.then_block)?;
            if let Some(else_branch) = &mut if_stmt.else_block {
                self.analyze(else_branch)?;
            }
            Ok(Type::Void)
        } else if is::<While>(node) {
            let while_stmt = cast_mut::<While>(node).unwrap();
            let cond_type = self.analyze(&mut while_stmt.condition)?;
            if matches!(cond_type, Type::Float) {
                while_stmt.condition = Box::new(BinaryOp {
                    typ: Type::Int,
                    lhs: take(&mut while_stmt.condition),
                    op: Op::Ne,
                    rhs: Box::new(Literal::Float(0.0)),
                });
            }

            self.analyze(&mut while_stmt.body)?;
            Ok(Type::Void)
        } else if is::<Return>(node) {
            // check whether the function return type matches
            let ret = cast_mut::<Return>(node).unwrap();
            if let Some(expr) = &mut ret.0 {
                let ret_typ = self.analyze(expr)?;
                let func_typ = self
                    .syms
                    .get(&self.current_func.as_ref().unwrap())
                    .unwrap()
                    .clone();
                let func_ret_typ = match func_typ {
                    Type::Function { return_type, .. } => *return_type,
                    _ => panic!("Current function is not a function type!"),
                };
                if (func_ret_typ == Type::Void) ^ (ret_typ == Type::Void) {
                    return Err(format!(
                        "Return type mismatch in function {}: expected {:?}, got {:?}",
                        self.current_func.as_ref().unwrap(),
                        func_ret_typ,
                        ret_typ
                    ));
                } else if func_ret_typ != ret_typ {
                    // insert implicit cast if necessary
                    ret.0 = Some(Box::new(UnaryOp {
                        typ: func_ret_typ.clone(),
                        op: Op::Cast(ret_typ, func_ret_typ.clone()),
                        operand: take(expr),
                    }));
                }
            }
            Ok(Type::Void)
        } else if is::<Assign>(node) {
            let assign = cast_mut::<Assign>(node).unwrap();
            let lhs_type = self.analyze(&mut assign.lhs)?;
            let rhs_type = self.analyze(&mut assign.rhs)?;
            // insert implicit cast if necessary
            if lhs_type != rhs_type {
                assign.rhs = Box::new(UnaryOp {
                    typ: lhs_type.clone(),
                    op: Op::Cast(rhs_type, lhs_type),
                    operand: take(&mut assign.rhs),
                });
            }

            Ok(Type::Void)
        } else {
            Ok(Type::Void)
        }
    }
}

impl Pass<Box<dyn Node>> for Semantic {
    fn run(&mut self) -> Result<Box<dyn Node>, String> {
        let mut node = self.node.take().unwrap();
        // create a scope for SysY lib functions, which is outermost scope
        self.syms.enter_scope();
        self.syms.insert(
            "getint".to_string(),
            Type::Function {
                return_type: Box::new(Type::Int),
                param_types: vec![],
            },
        );
        self.syms.insert(
            "getfloat".to_string(),
            Type::Function {
                return_type: Box::new(Type::Float),
                param_types: vec![],
            },
        );
        self.syms.insert(
            "getch".to_string(),
            Type::Function {
                return_type: Box::new(Type::Int),
                param_types: vec![],
            },
        );
        self.syms.insert(
            "getarray".to_string(),
            Type::Function {
                return_type: Box::new(Type::Int),
                param_types: vec![Type::Pointer {
                    base: Box::new(Type::Int),
                }],
            },
        );
        self.syms.insert(
            "getfarray".to_string(),
            Type::Function {
                return_type: Box::new(Type::Int),
                param_types: vec![Type::Pointer {
                    base: Box::new(Type::Float),
                }],
            },
        );
        self.syms.insert(
            "putint".to_string(),
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![Type::Int],
            },
        );
        self.syms.insert(
            "putfloat".to_string(),
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![Type::Float],
            },
        );
        self.syms.insert(
            "putch".to_string(),
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![Type::Int],
            },
        );
        self.syms.insert(
            "putarray".to_string(),
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![
                    Type::Int,
                    Type::Pointer {
                        base: Box::new(Type::Int),
                    },
                ],
            },
        );
        self.syms.insert(
            "putfarray".to_string(),
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![
                    Type::Int,
                    Type::Pointer {
                        base: Box::new(Type::Float),
                    },
                ],
            },
        );
        self.syms.insert(
            "putf".to_string(),
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![
                    Type::Pointer {
                        base: Box::new(Type::Char),
                    },
                    /*only store the string type, since the trailing params are dynamic according to the format string*/ 
                ],
            },
        );
        self.syms.insert(
            "starttime".to_string(),
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![],
            },
        );
        self.syms.insert(
            "stoptime".to_string(),
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![],
            },
        );
        self.analyze(&mut node)?;
        self.syms.exit_scope();
        Ok(node)
    }
}

// Array -> Pointer
pub fn decay(typ: Type) -> Result<Type, String> {
    match typ {
        Type::Array { base, dims } => {
            if dims.len() == 0 {
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
        },
        // do nothing for pointer type
        Type::Pointer {..} => Ok(typ),
        _ => Err(format!("Cannot decay non-array type: {:?}", typ)),
    }
}
