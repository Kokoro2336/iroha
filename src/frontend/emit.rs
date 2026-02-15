use crate::base::ir;
use crate::base::ir::*;
use crate::base::SYSY_LIB;
use crate::base::{Builder, BuilderContext, LoopInfo};
/**
 * Original IR generation.
 */
use crate::base::{Pass, SymbolTable, Type};
use crate::frontend::ast;
use crate::frontend::ast::*;
use crate::frontend::semantic::decay;
use crate::utils::{cast, is};

use std::collections::HashMap;

pub struct Emit<'a> {
    root: &'a Box<dyn Node>,
    builder: Builder,
    program: Program,

    // This time, for the convenience of recongizing global vars, we store a separate table for them.
    globals: HashMap<String, Operand>,
    // symbol -> OpId(for Alloca)
    syms: SymbolTable<String, Operand>,
    // we store the idx of current function
    current_function: Option<usize>,
    // original name -> promoted name
    mangled: HashMap<String, String>,

    // func name -> Func
    func_ids: HashMap<String, usize>,
    // var name -> OpId
    var_ids: HashMap<String, usize>,

    // counters
    counter: u32,
    // for naming string literals
    str_counter: u32,
}

macro_rules! context {
    ($self:ident) => {
        if let Some(func_idx) = $self.current_function {
            let func = &mut $self.program.funcs[func_idx];
            BuilderContext {
                cfg: Some(&mut func.cfg),
                dfg: Some(&mut func.dfg),
                globals: &mut $self.program.globals,
            }
        } else {
            BuilderContext {
                cfg: None,
                dfg: None,
                globals: &mut $self.program.globals,
            }
        }
    };
}

macro_rules! context_or_err {
    ($self:ident, $msg:expr) => {
        if let Some(func_idx) = $self.current_function {
            let func = &mut $self.program.funcs[func_idx];
            BuilderContext {
                cfg: Some(&mut func.cfg),
                dfg: Some(&mut func.dfg),
                globals: &mut $self.program.globals,
            }
        } else {
            return Err($msg.to_string());
        }
    };
}

pub(crate) use {context, context_or_err};

impl<'a> Emit<'a> {
    pub fn new(builder: Builder, root: &'a Box<dyn Node>) -> Self {
        Self {
            builder,
            syms: SymbolTable::new(),
            globals: HashMap::new(),
            root,
            program: Program::new(),
            current_function: None,
            mangled: HashMap::new(),
            func_ids: HashMap::new(),
            var_ids: HashMap::new(),
            counter: 0,
            str_counter: 0,
        }
    }

    pub fn emit(&mut self, node: &Box<dyn Node>) -> Result<Option<Operand>, String> {
        if let Some(fn_decl) = cast::<FnDecl>(&**node) {
            crate::debug::info!("Emitting function: {}", fn_decl.name);
            // create new function
            self.current_function = Some(self.program.funcs.add(Function::new(
                fn_decl.name.clone(),
                false,
                fn_decl.typ.clone(),
            ))?);

            // store function id
            if let Some(func_id) = self.current_function {
                self.func_ids.insert(fn_decl.name.clone(), func_id);
            }

            {
                // get and store arguments
                // shadow the ctx to use function's cfg/dfg
                // in other branches, the ctx is already function's ctx
                let mut ctx = context_or_err!(self, "Function not found");

                //create new block for function
                let block_id = self.builder.create_new_block(&mut ctx)?;
                self.builder.set_current_block(block_id)?;
                // enter function scope
                self.syms.enter_scope();

                for (i, arg) in fn_decl.params.iter().enumerate() {
                    let get_arg = self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            arg.1.clone(),
                            vec![Attr::Name(arg.0.clone())],
                            OpData::GetArg(Operand::ParamId(i as u32)),
                        ),
                    )?;
                    let alloca = self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            Type::Pointer {
                                base: Box::new(arg.1.clone()),
                            },
                            vec![Attr::Name(arg.0.clone())],
                            OpData::Alloca(arg.1.size_in_bytes()),
                        ),
                    )?;
                    self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            Type::Void,
                            vec![],
                            OpData::Store {
                                addr: alloca.clone(),
                                value: get_arg,
                            },
                        ),
                    )?;
                    // insert into symbol table
                    self.syms.insert(arg.0.clone(), alloca);
                }

                // create new block for body
                let body_block_id = self.builder.create_new_block(&mut ctx)?;
                // jump to body block
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Void,
                        vec![],
                        OpData::Jump {
                            target_bb: body_block_id.clone(),
                        },
                    ),
                )?;
                // set current block to body block
                self.builder.set_current_block(body_block_id)?;
            }

            // parse the function body
            self.emit(&fn_decl.body)?;
            // exit function scope
            self.syms.exit_scope();
            return Ok(None);
        } else if let Some(block) = cast::<Block>(&**node) {
            // enter scope
            self.syms.enter_scope();
            block
                .statements
                .iter()
                .try_for_each(|stmt| -> Result<(), String> {
                    self.emit(stmt)?;
                    Ok(())
                })?;
            // exit scope
            self.syms.exit_scope();
        } else if let Some(var_decl) = cast::<VarDecl>(&**node) {
            // Global alloca
            if var_decl.is_global {
                let mut ctx = context!(self);
                let alloca = self.builder.create(
                    // use program.globals DFG
                    &mut ctx,
                    ir::Op::new(
                        Type::Pointer {
                            base: Box::new(var_decl.typ.clone()),
                        },
                        vec![
                            // treat all the global vars as Array.
                            Attr::GlobalArray {
                                name: var_decl.name.clone(),
                                mutable: var_decl.mutable,
                                // cast to pointer typ
                                typ: var_decl.typ.clone(),
                                values: if let Some(init_value) = &var_decl.init_value {
                                    if let Some(lit) = cast::<Literal>(&**init_value) {
                                        vec![lit.clone()]
                                    } else {
                                        return Err(format!(
                                            "Global VarDecl init_value is not Literal. Varname: {}",
                                            var_decl.name
                                        ));
                                    }
                                } else {
                                    // Global values' initializer can't be None here(initializer added in Parse)
                                    return Err(format!(
                                        "Global VarDecl has no init_value. Varname: {}",
                                        var_decl.name
                                    ));
                                },
                            },
                            Attr::Name(var_decl.name.clone()),
                        ],
                        OpData::GlobalAlloca(var_decl.typ.size_in_bytes()),
                    ),
                )?;
                // insert into globals table. If the var is global, then the symbol table must be at global scope.
                self.globals.insert(var_decl.name.clone(), alloca);
            } else {
                let alloca = {
                    let mut ctx = context!(self);
                    // Alloca
                    self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            // cast to pointer too
                            Type::Pointer {
                                base: Box::new(var_decl.typ.clone()),
                            },
                            vec![Attr::Name(var_decl.name.clone()), Attr::Promotion],
                            OpData::Alloca(var_decl.typ.size_in_bytes()),
                        ),
                    )?
                };
                // insert into symbol table
                self.syms.insert(var_decl.name.clone(), alloca.clone());
                // if has init value, create store
                if let Some(init_val) = &var_decl.init_value {
                    let op_id = self.emit(init_val)?;
                    // Re-acquire ctx after emit
                    let mut ctx = context_or_err!(self, "Local variable init outside function");

                    self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            Type::Void,
                            vec![],
                            OpData::Store {
                                addr: alloca,
                                value: op_id.unwrap(),
                            },
                        ),
                    )?;
                }
                // If no init value, do nothing (the value is undefined)
            }
            return Ok(None);
        } else if let Some(var_array) = cast::<VarArray>(&**node) {
            if var_array.is_global {
                let mut ctx = context!(self);
                // Global alloca
                // use ConstArray to represent all the global array, but it doesn't mean .
                let alloca = self.builder.create(
                    // use program.globals DFG
                    &mut ctx,
                    ir::Op::new(
                        // wrap it with pointer
                        Type::Pointer {
                            base: Box::new(var_array.typ.clone()),
                        },
                        vec![
                            Attr::GlobalArray {
                                name: var_array.name.clone(),
                                mutable: true,
                                typ: var_array.typ.clone(),
                                values: if let Some(init_values) = &var_array.init_values {
                                    init_values
                                        .iter()
                                        .map(|v| {
                                            if let Some(lit) = cast::<Literal>(&**v) {
                                                lit.clone()
                                            } else {
                                                panic!("Global VarArray init_values contain non-Literal. Varname: {}", var_array.name);
                                            }
                                        })
                                        .collect()
                                } else {
                                    // panic
                                    return Err(format!("Global VarArray has no init_values. Varname: {}", var_array.name));
                                },
                            },
                            Attr::Name(var_array.name.clone()),
                        ],
                        OpData::GlobalAlloca(var_array.typ.size_in_bytes()),
                    ),
                )?;
                // insert into globals table. If the var is global, then the symbol table must because at global scope.
                self.globals.insert(var_array.name.clone(), alloca);
            } else {
                let total_size = var_array.typ.size_in_bytes();
                let alloca = {
                    let mut ctx = context!(self);
                    self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            Type::Pointer {
                                base: Box::new(var_array.typ.clone()),
                            },
                            vec![Attr::Name(var_array.name.clone())],
                            OpData::Alloca(total_size),
                        ),
                    )?
                };
                // insert the pointer of the array into symbol table
                self.syms.insert(var_array.name.clone(), alloca.clone());
                // if has init values, create stores
                if let Some(init_values) = &var_array.init_values {
                    let (dims, base) = match &var_array.typ {
                        Type::Array { dims, base } => (dims.clone(), *base.clone()),
                        _ => {
                            return Err("VarArray typ is not Array".to_string());
                        }
                    };
                    let ranges = MultiDimIter::new(dims.iter().map(|&d| d as usize).collect());
                    for range in ranges {
                        // evaluate the init value
                        let idx = range.iter().enumerate().fold(0usize, |acc, (i, &x)| {
                            if i < range.len() - 1 {
                                (acc + x) * dims[i + 1] as usize
                            } else {
                                acc + x
                            }
                        });
                        let op_id = self.emit(&init_values[idx])?;

                        // Re-acquire ctx
                        let mut ctx = context_or_err!(self, "Local array init outside function");

                        // evaluate the address
                        let addr = self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Pointer {
                                    base: Box::new(base.clone()),
                                },
                                vec![],
                                OpData::GEP {
                                    base: alloca.clone(),
                                    indices: std::iter::once(Operand::Index(0))
                                        .chain(range.iter().map(|&i| Operand::Index(i)))
                                        .collect(),
                                },
                            ),
                        )?;
                        // store
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Store {
                                    addr,
                                    value: op_id.unwrap(),
                                },
                            ),
                        )?;
                    }
                    // TODO: when the trailing zeroes reach some kind of limit, we add a loop to init them.
                }
            }
        } else if let Some(const_array) = cast::<ConstArray>(&**node) {
            let func_name_opt = if let Some(current_func) = self.current_function {
                Some(self.program.funcs[current_func].name.clone())
            } else {
                None
            };

            let name = if let Some(func_name) = func_name_opt {
                // promote the const array to global
                // generate mangled name
                let mangled_name = format!(
                    "__const_{}_{}_{}",
                    func_name, const_array.name, self.counter
                );
                // update the counter
                self.counter += 1;
                // insert into mangled table
                self.mangled
                    .insert(const_array.name.clone(), mangled_name.clone());
                mangled_name
            } else {
                const_array.name.clone()
            };

            let mut ctx = context!(self);

            // Global alloca
            let alloca = self.builder.create(
                // use program.globals DFG
                &mut ctx,
                ir::Op::new(
                    Type::Pointer {
                        base: Box::new(const_array.typ.clone()),
                    },
                    vec![
                        Attr::GlobalArray {
                            name: name.clone(),
                            mutable: false,
                            typ: const_array.typ.clone(),
                            values: const_array
                                .init_values
                                .iter()
                                .map(|v| {
                                    if let Some(lit) = cast::<Literal>(&**v) {
                                        lit.clone()
                                    } else {
                                        panic!(
                                            "ConstArray init_values contain non-Literal: {:?}",
                                            v
                                        );
                                    }
                                })
                                .collect(),
                        },
                        Attr::Name(name.clone()),
                    ],
                    OpData::GlobalAlloca(const_array.typ.size_in_bytes()),
                ),
            )?;
            // insert into globals table. If the var is global, then the symbol table must because at global scope.
            self.globals.insert(name, alloca);
        } else if let Some(ret) = cast::<Return>(&**node) {
            if let Some(ret_val) = &ret.0 {
                let op_id = self.emit(ret_val)?;
                let mut ctx = context_or_err!(self, "Return outside function");

                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Void,
                        vec![],
                        OpData::Ret {
                            value: Some(op_id.unwrap()),
                        },
                    ),
                )?;
            } else {
                let mut ctx = context_or_err!(self, "Return outside function");

                self.builder.create(
                    &mut ctx,
                    ir::Op::new(Type::Void, vec![], OpData::Ret { value: None }),
                )?;
            }
        } else if let Some(if_stmt) = cast::<If>(&**node) {
            let (then_block, else_block, end_block) = {
                let mut ctx = context_or_err!(self, "If statement outside function");

                // create blocks first
                (
                    self.builder.create_new_block(&mut ctx)?,
                    if if_stmt.else_block.is_some() {
                        Some(self.builder.create_new_block(&mut ctx)?)
                    } else {
                        None
                    },
                    self.builder.create_new_block(&mut ctx)?,
                )
            };

            // evaluate the codition
            let cond_op = self.emit(&if_stmt.condition)?;

            {
                let mut ctx = context_or_err!(self, "If statement outside function");
                // create branch instructions
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Void,
                        vec![],
                        OpData::Br {
                            cond: cond_op.unwrap(),
                            then_bb: then_block.clone(),
                            else_bb: else_block.clone(),
                        },
                    ),
                )?;
            }

            // then block_id
            self.builder.set_current_block(then_block)?;
            self.emit(&if_stmt.then_block)?;

            // Re-acquire ctx
            {
                let mut ctx = context_or_err!(self, "If statement outside function");

                // Add jump to end_block if not terminated
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Void,
                        vec![],
                        OpData::Jump {
                            target_bb: end_block.clone(),
                        },
                    ),
                )?;
            }

            // else block_id
            if let Some(else_blk) = else_block {
                self.builder.set_current_block(else_blk)?;
                self.emit(if_stmt.else_block.as_ref().unwrap())?;

                // Re-acquire ctx
                let mut ctx = context_or_err!(self, "If statement outside function");

                // Add jump to end_block if not terminated
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Void,
                        vec![],
                        OpData::Jump {
                            target_bb: end_block.clone(),
                        },
                    ),
                )?;
            }

            // set current block to end_block
            self.builder.set_current_block(end_block)?;
        } else if let Some(while_stmt) = cast::<While>(&**node) {
            let (while_entry, while_body, while_end) = {
                let mut ctx = context_or_err!(self, "While statement outside function");

                // create blocks
                let while_entry = self.builder.create_new_block(&mut ctx)?;
                let while_body = self.builder.create_new_block(&mut ctx)?;
                let while_end = self.builder.create_new_block(&mut ctx)?;

                // jump to while_entry
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Void,
                        vec![],
                        OpData::Jump {
                            target_bb: while_entry.clone(),
                        },
                    ),
                )?;
                (while_entry, while_body, while_end)
            };

            // while_entry block
            self.builder.set_current_block(while_entry.clone())?;
            let cond_op = self.emit(&while_stmt.condition)?;

            // Re-acquire ctx
            {
                let mut ctx = context_or_err!(self, "While statement outside function");

                // create branch instruction
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Void,
                        vec![],
                        OpData::Br {
                            cond: cond_op.unwrap(),
                            then_bb: while_body.clone(),
                            else_bb: Some(while_end.clone()),
                        },
                    ),
                )?;
            }

            // while_body block
            self.builder.set_current_block(while_body)?;
            // push loop info
            self.builder.push_loop(LoopInfo {
                while_entry: Some(while_entry.clone()),
                end_block: Some(while_end.clone()),
            });
            self.emit(&while_stmt.body)?;
            // pop loop info
            self.builder.pop_loop();

            // Re-acquire ctx
            let mut ctx = context_or_err!(self, "While statement outside function");

            // jump back to while_entry
            self.builder.create(
                &mut ctx,
                ir::Op::new(
                    Type::Void,
                    vec![],
                    OpData::Jump {
                        target_bb: while_entry,
                    },
                ),
            )?;

            // set current block to while_end
            self.builder.set_current_block(while_end.clone())?;
        } else if cast::<Break>(&**node).is_some() {
            let loop_info = self
                .builder
                .loop_stack
                .last()
                .ok_or("Break statement not inside a loop")?;
            let mut ctx = context_or_err!(self, "Break statement not inside a function");

            self.builder.create(
                &mut ctx,
                ir::Op::new(
                    Type::Void,
                    vec![],
                    OpData::Jump {
                        target_bb: loop_info.end_block.clone().unwrap(),
                    },
                ),
            )?;
        } else if cast::<Continue>(&**node).is_some() {
            let loop_info = self
                .builder
                .loop_stack
                .last()
                .ok_or("Continue statement not inside a loop")?;

            let mut ctx = context_or_err!(self, "Continue statement not inside a function");

            self.builder.create(
                &mut ctx,
                ir::Op::new(
                    Type::Void,
                    vec![],
                    OpData::Jump {
                        target_bb: loop_info.while_entry.clone().unwrap(),
                    },
                ),
            )?;
        } else if let Some(assign_stmt) = cast::<Assign>(&**node) {
            crate::debug::info!("Emitting assignment statement: {:?}", assign_stmt);
            // emit rhs first
            let rhs_op = self.emit(&assign_stmt.rhs)?;
            // emit lhs
            let lhs_op = self.emit(&assign_stmt.lhs)?;

            // create store
            let mut ctx = context!(self);
            self.builder.create(
                &mut ctx,
                ir::Op::new(
                    Type::Void,
                    vec![],
                    OpData::Store {
                        addr: lhs_op.unwrap(),
                        value: rhs_op.unwrap(),
                    },
                ),
            )?;
        } else if let Some(var_access) = cast::<VarAccess>(&**node) {
            // remember, only address.
            if let Some(global_id) = self.globals.get(&var_access.name) {
                return Ok(Some(global_id.clone()));
            } else if let Some(ptr_addr) = self.syms.get(&var_access.name) {
                return Ok(Some(ptr_addr.clone()));
            } else {
                return Err(format!(
                    "VarAccess: variable {} not found in syms or globals",
                    var_access.name
                ));
            }
        } else if let Some(array_access) = cast::<ArrayAccess>(&**node) {
            // emit indices first
            let mut index_ops = vec![];
            for index in &array_access.indices {
                let op = self.emit(index)?;
                index_ops.push(op.unwrap());
            }

            let mut ctx = context_or_err!(self, "Array access outside function");

            // find whether the array is global or local
            let array_name = &array_access.name;

            // get the addr and the ptr_typ
            // array_access store the base type, so we need to wrap it with pointer
            let typ = Type::Pointer {
                base: Box::new(array_access.typ.clone()),
            };
            let ptr_addr = if let Some(global_id) = self.globals.get(array_name) {
                // global array
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        typ,
                        vec![],
                        OpData::GEP {
                            base: global_id.clone(),
                            indices: index_ops
                                .splice(0..0, std::iter::once(Operand::Int(0)))
                                .collect(),
                        },
                    ),
                )?
            } else if let Some(mangled_name) = self.mangled.get(array_name) {
                // promoted local const array
                let global_id = self.globals.get(mangled_name).ok_or(format!(
                    "ArrayAccess: promoted const array {} not found in globals",
                    mangled_name
                ))?;
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        typ.clone(),
                        vec![],
                        OpData::GEP {
                            base: global_id.clone(),
                            indices: index_ops
                                .splice(0..0, std::iter::once(Operand::Int(0)))
                                .collect(),
                        },
                    ),
                )?
            } else {
                // normal local var array
                let ptr_addr = self.syms.get(array_name).ok_or(format!(
                    "ArrayAccess: local array {} not found in syms",
                    array_name
                ))?;
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        typ.clone(),
                        vec![],
                        OpData::GEP {
                            base: ptr_addr.clone(),
                            indices: index_ops
                                .splice(0..0, std::iter::once(Operand::Int(0)))
                                .collect(),
                        },
                    ),
                )?
            };
            return Ok(Some(ptr_addr));
        } else if let Some(call) = cast::<Call>(&**node) {
            // evaluate arguments
            let mut arg_ops: Vec<Operand> = vec![];
            for arg in &call.args {
                let arg_op = self.emit(arg)?;
                arg_ops.push(arg_op.unwrap());
            }

            let mut ctx = context_or_err!(self, "Call outside function");

            // create call op_id
            let call_op = self.builder.create(
                &mut ctx,
                ir::Op::new(
                    call.typ.clone(),
                    vec![Attr::FuncName(call.func_name.clone())],
                    OpData::Call {
                        func: Operand::Func(self.func_ids[&call.func_name]),
                        args: arg_ops,
                    },
                ),
            )?;
            return Ok(Some(call_op));
        } else if let Some(binary_op) = cast::<BinaryOp>(&**node) {
            crate::debug::info!("Emitting binary operation: {:?}", binary_op);
            // And & Or need short-circuit evaluation, so we handle them separately.
            match &binary_op.op {
                ast::Op::And => {
                    // Allocate the space for result first
                    let (result_alloca, rhs_block, end_block) = {
                        let mut ctx = context_or_err!(self, "BinaryOp And outside function");
                        let result_alloca = self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Pointer {
                                    base: Box::new(Type::Int),
                                },
                                vec![],
                                OpData::Alloca(Type::Int.size_in_bytes()),
                            ),
                        )?;
                        // store 0 first
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Store {
                                    addr: result_alloca.clone(),
                                    value: Operand::Int(0),
                                },
                            ),
                        )?;
                        // create 2 blocks for short-circuit
                        (
                            result_alloca,
                            self.builder.create_new_block(&mut ctx)?,
                            self.builder.create_new_block(&mut ctx)?,
                        )
                    };

                    // evaluate lhs
                    let lhs_op = self.emit(&binary_op.lhs)?;
                    // branch based on lhs
                    {
                        let mut ctx = context_or_err!(self, "BinaryOp And outside function");
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Br {
                                    cond: lhs_op.unwrap(),
                                    then_bb: rhs_block.clone(),
                                    else_bb: Some(end_block.clone()),
                                },
                            ),
                        )?;
                        // rhs block
                        self.builder.set_current_block(rhs_block)?;
                    }

                    let rhs_op = self.emit(&binary_op.rhs)?;
                    // store rhs to result_alloca
                    {
                        let mut ctx = context_or_err!(self, "BinaryOp And outside function");
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Store {
                                    addr: result_alloca.clone(),
                                    value: rhs_op.unwrap(),
                                },
                            ),
                        )?;
                        // jump to end block
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Jump {
                                    target_bb: end_block.clone(),
                                },
                            ),
                        )?;
                    }
                    // end block
                    self.builder.set_current_block(end_block)?;
                    // load result
                    let mut ctx = context_or_err!(self, "BinaryOp And outside function");
                    let load_result = self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            Type::Int,
                            vec![],
                            OpData::Load {
                                addr: result_alloca.clone(),
                            },
                        ),
                    )?;
                    return Ok(Some(load_result));
                }
                ast::Op::Or => {
                    // Allocate the space for result first
                    let (result_alloca, rhs_block, end_block) = {
                        let mut ctx = context_or_err!(self, "BinaryOp Or outside function");
                        let result_alloca = self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Pointer {
                                    base: Box::new(Type::Int),
                                },
                                vec![],
                                OpData::Alloca(Type::Int.size_in_bytes()),
                            ),
                        )?;
                        // store 1 first
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Store {
                                    addr: result_alloca.clone(),
                                    value: Operand::Int(1),
                                },
                            ),
                        )?;
                        // create 2 blocks for short-circuit
                        (
                            result_alloca,
                            self.builder.create_new_block(&mut ctx)?,
                            self.builder.create_new_block(&mut ctx)?,
                        )
                    };

                    {
                        // evaluate lhs
                        let lhs_op = self.emit(&binary_op.lhs)?;
                        // branch based on lhs
                        let mut ctx = context_or_err!(self, "BinaryOp Or outside function");
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Br {
                                    cond: lhs_op.unwrap(),
                                    then_bb: end_block.clone(),
                                    else_bb: Some(rhs_block.clone()),
                                },
                            ),
                        )?;
                    }

                    // rhs block
                    self.builder.set_current_block(rhs_block)?;
                    let rhs_op = self.emit(&binary_op.rhs)?;
                    // store rhs to result_alloca
                    {
                        let mut ctx = context_or_err!(self, "BinaryOp Or outside function");
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Store {
                                    addr: result_alloca.clone(),
                                    value: rhs_op.unwrap(),
                                },
                            ),
                        )?;
                        // jump to end block
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Jump {
                                    target_bb: end_block.clone(),
                                },
                            ),
                        )?;
                    }
                    // end block
                    self.builder.set_current_block(end_block)?;
                    // load result
                    let mut ctx = context_or_err!(self, "BinaryOp Or outside function");
                    let load_result = self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            Type::Int,
                            vec![],
                            OpData::Load {
                                addr: result_alloca.clone(),
                            },
                        ),
                    )?;
                    return Ok(Some(load_result));
                }
                _ => {}
            }

            let mut lhs = self.emit(&binary_op.lhs)?;
            if is::<VarAccess>(&*binary_op.lhs) || is::<ArrayAccess>(&*binary_op.lhs) {
                // load lhs
                let mut ctx = context_or_err!(self, "BinaryOp lhs load outside function");
                let load_lhs = self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        binary_op.typ.clone(),
                        vec![],
                        OpData::Load { addr: lhs.unwrap() },
                    ),
                )?;
                // replace lhs with loaded value
                lhs = Some(load_lhs);
            }
            let mut rhs = self.emit(&binary_op.rhs)?;
            if is::<VarAccess>(&*binary_op.rhs) || is::<ArrayAccess>(&*binary_op.rhs) {
                // load rhs
                let mut ctx = context_or_err!(self, "BinaryOp rhs load outside function");
                let load_rhs = self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        binary_op.typ.clone(),
                        vec![],
                        OpData::Load { addr: rhs.unwrap() },
                    ),
                )?;
                // replace rhs with loaded value
                rhs = Some(load_rhs);
            }

            let mut ctx: BuilderContext<'_> = context_or_err!(self, "BinaryOp outside function");

            // select Operator
            let typ = binary_op.typ.clone();
            let op_data = match &binary_op.op {
                ast::Op::Add => {
                    if typ == Type::Int {
                        OpData::AddI {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::AddF {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                ast::Op::Sub => {
                    if typ == Type::Int {
                        OpData::SubI {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::SubF {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                ast::Op::Mul => {
                    if typ == Type::Int {
                        OpData::MulI {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::MulF {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                ast::Op::Div => {
                    if typ == Type::Int {
                        OpData::DivI {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::DivF {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                ast::Op::Mod => {
                    if typ == Type::Int {
                        OpData::ModI {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        return Err("Mod operator only supports Int type".to_string());
                    }
                }
                ast::Op::And => {
                    if typ == Type::Int {
                        // short circuit
                        OpData::And {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        return Err("And operator only supports Int type".to_string());
                    }
                }
                ast::Op::Or => {
                    if typ == Type::Int {
                        OpData::Or {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        return Err("Or operator only supports Int type".to_string());
                    }
                }
                ast::Op::Eq => {
                    if typ == Type::Int {
                        OpData::SEq {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::OEq {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                ast::Op::Ne => {
                    if typ == Type::Int {
                        OpData::SNe {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::ONe {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                ast::Op::Gt => {
                    if typ == Type::Int {
                        OpData::SGt {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::OGt {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                ast::Op::Lt => {
                    if typ == Type::Int {
                        OpData::SLt {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::OLt {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                ast::Op::Ge => {
                    if typ == Type::Int {
                        OpData::SGe {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::OGe {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                ast::Op::Le => {
                    if typ == Type::Int {
                        OpData::SLe {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    } else {
                        OpData::OLe {
                            lhs: lhs.unwrap(),
                            rhs: rhs.unwrap(),
                        }
                    }
                }
                // shift ops only appear in strength reduction, not in source code.
                _ => {
                    return Err(format!(
                        "Unsupported binary operator {:?} in Emit",
                        binary_op.op
                    ));
                }
            };

            // create the op
            let bin_op = self
                .builder
                .create(&mut ctx, ir::Op::new(typ.clone(), vec![], op_data))?;
            return Ok(Some(bin_op));
        } else if let Some(unary_op) = cast::<UnaryOp>(&**node) {
            let mut operand = self.emit(&unary_op.operand)?;
            // load operand
            if is::<VarAccess>(&*unary_op.operand) || is::<ArrayAccess>(&*unary_op.operand) {
                let mut ctx = context_or_err!(self, "UnaryOp operand load outside function");
                let load_operand = self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        unary_op.typ.clone(),
                        vec![],
                        OpData::Load {
                            addr: operand.unwrap(),
                        },
                    ),
                )?;
                // replace operand with loaded value
                operand = Some(load_operand);
            }

            let mut ctx = context_or_err!(self, "UnaryOp outside function");

            // select Operator
            let typ = unary_op.typ.clone();
            let op_data = match unary_op.op.clone() {
                // unary op
                ast::Op::Plus => unreachable!("Unary plus should have been eliminated earlier"),
                ast::Op::Minus => {
                    if typ == Type::Int {
                        // 0 - rhs
                        OpData::SubI {
                            lhs: Operand::Int(0),
                            rhs: operand.unwrap(),
                        }
                    } else {
                        // 0.0 - rhs
                        OpData::SubF {
                            lhs: Operand::Float(0.0),
                            rhs: operand.unwrap(),
                        }
                    }
                }
                ast::Op::Not => {
                    if typ == Type::Int {
                        // 1 - rhs
                        OpData::SNe {
                            lhs: operand.unwrap(),
                            rhs: Operand::Int(0),
                        }
                    } else {
                        return Err(format!(
                            "Not operator only supports Int type: {:?}",
                            unary_op
                        ));
                    }
                }

                // cast
                ast::Op::Cast(ref from, ref to) => match (from, to) {
                    (Type::Int, Type::Float) => OpData::Sitofp {
                        value: operand.unwrap(),
                    },
                    (Type::Float, Type::Int) => OpData::Fptosi {
                        value: operand.unwrap(),
                    },
                    _ => {
                        return Err(format!("Unsupported cast from {:?} to {:?}", from, to));
                    }
                },

                _ => unreachable!("Unsupported unary operator in Emit: {:?}", unary_op),
            };

            // create the op
            let un_op = self
                .builder
                .create(&mut ctx, ir::Op::new(typ.clone(), vec![], op_data))?;
            return Ok(Some(un_op));
        } else if let Some(literal) = cast::<Literal>(&**node) {
            let mut ctx = context!(self);

            match literal {
                Literal::Int(val) => {
                    return Ok(Some(Operand::Int(*val)));
                }
                Literal::Float(val) => {
                    return Ok(Some(Operand::Float(*val)));
                }
                Literal::String(string) => {
                    // create a global u8 ConstArray
                    // update str_counter
                    self.str_counter += 1;
                    // create global alloca
                    let typ = Type::Array {
                        base: Box::new(Type::Char),
                        dims: vec![(string.len() + 1) as u32],
                    };
                    let global_alloca = self.builder.create(
                        // use program.globals DFG
                        &mut ctx,
                        ir::Op::new(
                            Type::Pointer {
                                base: Box::new(typ.clone()),
                            },
                            vec![Attr::GlobalArray {
                                name: "".to_string(),
                                typ: typ.clone(),
                                mutable: false,
                                values: string
                                    .chars()
                                    .map(|c| Literal::Int(c as i32))
                                    // This chain adds the null terminator
                                    .chain(std::iter::once(Literal::Int(0)))
                                    .collect(),
                            }],
                            OpData::GlobalAlloca(typ.size_in_bytes()),
                        ),
                    )?;
                    // get the pointer right now
                    let ptr_typ = decay(typ)?;
                    // return the pointer OpId
                    let ptr_addr = self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            ptr_typ,
                            vec![],
                            OpData::GEP {
                                base: global_alloca,
                                indices: vec![
                                    Operand::Int(0),
                                    /* The first element's addr */ Operand::Int(0),
                                ],
                            },
                        ),
                    )?;
                    return Ok(Some(ptr_addr));
                }
            }
        }
        // ignore empty
        Ok(None)
    }
}

impl Pass<Program> for Emit<'_> {
    fn run(&mut self) -> Result<Program, String> {
        let root = self.root;
        // Emit declare ops for SysY lib first
        SYSY_LIB.with(|lib| -> Result<(), String> {
            let mut ctx = context!(self);
            for (name, typ) in lib.iter() {
                // Add it in globals first
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Void,
                        vec![],
                        OpData::Declare {
                            name: name.to_string(),
                            typ: typ.clone(),
                        },
                    ),
                )?;
            }
            for (name, typ) in lib.iter() {
                // Alloc space for the function in Call Graph
                let func_id =
                    self.program
                        .funcs
                        .add(Function::new(name.to_string(), true, typ.clone()))?;
                // Add it in func_ids for later call lookup
                self.func_ids.insert(name.to_string(), func_id);
            }
            Ok(())
        })?;
        self.emit(root)?;
        Ok(std::mem::take(&mut self.program))
    }
}

/// A tool to iterate over all coordinates of a multi-dimensional array.
/// Order: Row-major (C-style), last index changes fastest.
pub struct MultiDimIter {
    dims: Vec<usize>,
    curr: Vec<usize>,
    done: bool,
}

impl MultiDimIter {
    pub fn new(dims: Vec<usize>) -> Self {
        // Handle the edge case of 0-sized dimensions or empty dimensions
        let is_empty = dims.is_empty() || dims.contains(&0);

        Self {
            dims: dims.to_vec(),
            // Initialize indices to all zeros
            curr: vec![0; dims.len()],
            done: is_empty,
        }
    }
}

impl Iterator for MultiDimIter {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        // 1. Snapshot the current state to return later
        let result = self.curr.clone();

        // 2. Calculate the NEXT state (The "Odometer" logic)
        // We start from the rightmost dimension (last index)
        let mut i = self.dims.len();
        self.done = true; // Assume done unless we find a dimension to increment

        while i > 0 {
            i -= 1;
            self.curr[i] += 1;

            if self.curr[i] < self.dims[i] {
                // We successfully incremented this digit without overflow.
                // Stop carrying and continue iteration next time.
                self.done = false;
                break;
            } else {
                // Overflow! Reset this digit to 0 and carry over to the left.
                self.curr[i] = 0;
            }
        }

        Some(result)
    }
}
