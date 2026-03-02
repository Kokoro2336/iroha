use crate::base::ir;
use crate::base::ir::*;
use crate::base::SYSY_LIB;
use crate::base::{context, context_or_err};
use crate::base::{Builder, BuilderContext, LoopInfo};
use crate::base::{Pass, SymbolTable, Type};
use crate::frontend::ast;
use crate::frontend::ast::*;
use crate::frontend::semantic::decay;

use std::collections::HashMap;

pub struct Emit {
    ast: AST,
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

    // counters
    counter: u32,
    // for naming string literals
    str_counter: u32,
}

impl Emit {
    pub fn new(ast: AST) -> Self {
        Self {
            ast,
            builder: Builder::new(),
            syms: SymbolTable::new(),
            globals: HashMap::new(),
            program: Program::new(),
            current_function: None,
            mangled: HashMap::new(),
            func_ids: HashMap::new(),
            counter: 0,
            str_counter: 0,
        }
    }

    pub fn get_type(&self, operand: &Operand) -> Type {
        let current_func = match self.current_function {
            Some(idx) => &self.program.funcs[idx],
            None => panic!("get_type: not in a function"),
        };
        let dfg = &current_func.dfg;
        let globals = &self.program.globals;
        match operand {
            Operand::Value(id) => dfg[*id].typ.clone(),
            Operand::Global(id) => globals[*id].typ.clone(),
            Operand::Param { typ, .. } => typ.clone(),
            Operand::Int(_) => Type::Int,
            Operand::Float(_) => Type::Float,
            Operand::Bool(_) => Type::Bool,
            Operand::Undefined | Operand::Func(_) | Operand::Reg(_) | Operand::BB(_) => {
                unreachable!("Not allowed to get type of operand: {:?}", operand)
            }
        }
    }

    fn has_active_insertion_point(&self) -> bool {
        self.builder.current_block.is_some()
    }

    fn current_block_has_terminator(&self) -> bool {
        let current_func = match self.current_function {
            Some(idx) => &self.program.funcs[idx],
            None => return false,
        };
        let current_block = match &self.builder.current_block {
            Some(block) => block,
            None => return false,
        };

        let bb = &current_func.cfg[current_block.get_bb_id()];
        let Some(last_op) = bb.cur.last() else {
            return false;
        };
        matches!(
            current_func.dfg[last_op.get_op_id()].data,
            OpData::Br { .. } | OpData::Jump { .. } | OpData::Ret { .. }
        )
    }

    // This method is used to insert terminator which does not block the emitting of following instructions, such as conditional branch in the middle of if-else.
    // Check whether the current block already has a terminator, if not, insert one with the given OpData.
    fn insert_terminator_if_needed(&mut self, op_data: OpData) {
        if !self.has_active_insertion_point() || self.current_block_has_terminator() {
            return;
        }

        let mut ctx = context_or_err!(self, "Terminator insertion outside function");
        self.builder
            .create(&mut ctx, ir::Op::new(Type::Void, vec![], op_data));
    }

    // This method is used to insert terminator which blocks the emitting of following instructions, such as return, break, continue and goto.
    fn insert_terminator_and_unplug(&mut self, op_data: OpData) {
        self.insert_terminator_if_needed(op_data);
        self.builder.current_block = None;
        self.builder.current_inst = None;
    }

    pub fn emit(&mut self, node_id: NodeId) -> Option<Operand> {
        fn flat_to_indices(index: usize, dims: &[u32]) -> Vec<usize> {
            if dims.is_empty() {
                return vec![];
            }
            let mut rest = index;
            let mut indices = vec![0usize; dims.len()];
            for i in 0..dims.len() {
                let stride = if i + 1 >= dims.len() {
                    1usize
                } else {
                    dims[(i + 1)..].iter().product::<u32>() as usize
                };
                indices[i] = rest / stride;
                rest %= stride;
            }
            indices
        }

        fn literal_from_const_node(ast: &AST, node_id: NodeId) -> Literal {
            match &ast[node_id] {
                Node::Literal(lit) => lit.clone(),
                Node::UnaryOp { op, operand, .. } => {
                    let lit = match &ast[*operand] {
                        Node::Literal(lit) => lit,
                        _ => panic!(
                            "Global initializer cast operand must be literal: {:?}",
                            ast[*operand]
                        ),
                    };

                    // Remember, SysY doesn't have Bool literals.
                    match op {
                        ast::Op::Int2Float => match lit {
                            Literal::Int(i) => Literal::Float(*i as f32),
                            _ => panic!(
                                "Int2Float operand must be Int literal: {:?}",
                                ast[*operand]
                            ),
                        },
                        ast::Op::Float2Int => match lit {
                            Literal::Float(f) => Literal::Int(*f as i32),
                            _ => panic!(
                                "Float2Int operand must be Float literal: {:?}",
                                ast[*operand]
                            ),
                        },
                        _ => unreachable!("Only Int2Float and Float2Int should be used in global initializer casts"),
                    }
                }
                _ => panic!(
                    "Global initializer must be literal or cast literal: {:?}",
                    ast[node_id]
                ),
            }
        }

        fn node_value_type(ast: &AST, node_id: NodeId) -> Type {
            match &ast[node_id] {
                Node::VarAccess { typ, .. }
                | Node::ArrayAccess { typ, .. }
                | Node::Call { typ, .. }
                | Node::BinaryOp { typ, .. }
                | Node::UnaryOp { typ, .. } => typ.clone(),
                Node::Literal(Literal::Int(_)) => Type::Int,
                Node::Literal(Literal::Float(_)) => Type::Float,
                Node::Literal(Literal::String(_)) => Type::Pointer {
                    base: Box::new(Type::Char),
                },
                _ => panic!("Cannot derive value type from node: {:?}", ast[node_id]),
            }
        }

        fn emit_rval(this: &mut Emit, node_id: NodeId) -> Operand {
            let mut op = this.emit(node_id).unwrap_or_else(|| {
                panic!(
                    "Expected value node, got statement node: {:?}",
                    this.ast[node_id]
                )
            });

            let node_typ = NodeType::from(&this.ast[node_id]);
            match node_typ {
                NodeType::VarAccess => {
                    let typ = node_value_type(&this.ast, node_id);
                    let mut ctx = context_or_err!(this, "Value load outside function");
                    op = this.builder.create(
                        &mut ctx,
                        ir::Op::new(typ, vec![], OpData::Load { addr: op }),
                    );
                }
                NodeType::ArrayAccess => {
                    let typ = node_value_type(&this.ast, node_id);
                    match typ {
                        Type::Array { .. } => {
                            let mut ctx = context_or_err!(this, "Value load outside function");
                            // decay it.
                            op = this.builder.create(
                                &mut ctx,
                                ir::Op::new(
                                    decay(typ).unwrap(),
                                    vec![],
                                    OpData::GEP {
                                        base: op,
                                        indices: vec![Operand::Int(0), Operand::Int(0)],
                                    },
                                ),
                            );
                        }
                        _ => {
                            let mut ctx = context_or_err!(this, "Value load outside function");
                            op = this.builder.create(
                                &mut ctx,
                                ir::Op::new(typ, vec![], OpData::Load { addr: op }),
                            );
                        }
                    }
                }
                _ => {}
            }

            op
        }

        fn emit_cast(this: &mut Emit, operand: Operand, from: Type, to: Type) -> Operand {
            if from == to {
                return operand;
            }

            let op_data = match (&from, &to) {
                (Type::Bool, Type::Int) => OpData::Zext { value: operand },
                (Type::Int, Type::Bool) => OpData::SNe {
                    lhs: operand,
                    rhs: Operand::Int(0),
                },
                (Type::Float, Type::Bool) => OpData::ONe {
                    lhs: operand,
                    rhs: Operand::Float(0.0),
                },
                (Type::Bool, Type::Float) => OpData::Uitofp { value: operand },
                (Type::Int, Type::Float) => OpData::Sitofp { value: operand },
                (Type::Float, Type::Int) => OpData::Fptosi { value: operand },
                _ => panic!("Unsupported implicit cast in Emit: {:?} -> {:?}", from, to),
            };

            let mut ctx = context_or_err!(this, "Cast outside function");
            this.builder
                .create(&mut ctx, ir::Op::new(to, vec![], op_data))
        }

        match &self.ast[node_id] {
            Node::DeclAggr { decls } => {
                let ids: Vec<NodeId> = decls.clone();
                for id in ids {
                    self.emit(id);
                }
                None
            }
            Node::FnDecl {
                name,
                params,
                typ,
                body,
            } => {
                let name = name.clone();
                let params = params.clone();
                let typ = typ.clone();
                let body = *body;

                self.current_function = Some(self.program.funcs.add(Function::new(
                    name.clone(),
                    false,
                    typ.clone(),
                )));

                if let Some(func_id) = self.current_function {
                    self.func_ids.insert(name, func_id);
                }

                {
                    let mut ctx = context_or_err!(self, "Function not found");
                    let block_id = self.builder.create_new_block(&mut ctx);
                    self.builder.set_current_block(block_id);
                    self.syms.enter_scope();

                    for (i, (arg_name, arg_typ)) in params.iter().enumerate() {
                        let alloca = self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Pointer {
                                    base: Box::new(arg_typ.clone()),
                                },
                                if arg_typ.is_scalar() {
                                    vec![Attr::Name(arg_name.clone()), Attr::Promotion]
                                } else {
                                    vec![Attr::Name(arg_name.clone())]
                                },
                                OpData::Alloca(arg_typ.clone()),
                            ),
                        );
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Store {
                                    addr: alloca.clone(),
                                    value: Operand::Param {
                                        idx: i,
                                        name: arg_name.clone(),
                                        typ: arg_typ.clone(),
                                    },
                                },
                            ),
                        );
                        self.syms.insert(arg_name.clone(), alloca);
                    }

                    let body_block_id = self.builder.create_new_block(&mut ctx);
                    self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            Type::Void,
                            vec![],
                            OpData::Jump {
                                target_bb: body_block_id.clone(),
                            },
                        ),
                    );
                    self.builder.set_current_block(body_block_id);
                }

                self.emit(body);

                if self.has_active_insertion_point() && !self.current_block_has_terminator() {
                    match typ {
                        Type::Function { return_type, .. } => {
                            if !matches!(*return_type, Type::Void) {
                                // TODO: Add reachability check to determine whether the implicit return is actually reachable.
                            }
                        }
                        _ => panic!("Function type expected"),
                    }
                    self.insert_terminator_and_unplug(OpData::Ret { value: None });
                }

                self.syms.exit_scope();
                None
            }
            Node::Block { statements } => {
                let ids: Vec<NodeId> = statements.clone();
                self.syms.enter_scope();
                for stmt in ids {
                    self.emit(stmt);
                }
                self.syms.exit_scope();
                None
            }
            Node::VarDecl {
                name,
                typ,
                is_global,
                mutable,
                init_value,
            } => {
                let name = name.clone();
                let typ = typ.clone();
                let is_global = *is_global;
                let mutable = *mutable;
                let init_value = *init_value;

                if is_global {
                    let init_literals = if let Some(init_id) = init_value {
                        Some(vec![literal_from_const_node(&self.ast, init_id)])
                    } else {
                        None
                    };

                    let mut ctx = context!(self);
                    let alloca = self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            Type::Pointer {
                                base: Box::new(typ.clone()),
                            },
                            vec![
                                Attr::GlobalArray {
                                    name: name.clone(),
                                    mutable,
                                    typ: typ.clone(),
                                    values: init_literals,
                                },
                                Attr::Name(name.clone()),
                            ],
                            OpData::GlobalAlloca(typ.size_in_bytes()),
                        ),
                    );
                    self.globals.insert(name, alloca);
                } else {
                    if self.current_function.is_some() && !self.has_active_insertion_point() {
                        return None;
                    }
                    let alloca = {
                        let mut ctx = context!(self);
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Pointer {
                                    base: Box::new(typ.clone()),
                                },
                                vec![Attr::Name(name.clone()), Attr::Promotion],
                                OpData::Alloca(typ.clone()),
                            ),
                        )
                    };
                    self.syms.insert(name, alloca.clone());

                    if let Some(init_id) = init_value {
                        let value = emit_rval(self, init_id);
                        let mut ctx = context_or_err!(self, "Local variable init outside function");
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Void,
                                vec![],
                                OpData::Store {
                                    addr: alloca,
                                    value,
                                },
                            ),
                        );
                    }
                }
                None
            }
            Node::VarArray {
                name,
                is_global,
                typ,
                init_values,
            } => {
                let name = name.clone();
                let is_global = *is_global;
                let typ = typ.clone();
                let init_values = init_values.clone();

                if is_global {
                    let values = if let Some(ids) = init_values {
                        let mut vals = vec![];
                        for id in ids {
                            vals.push(literal_from_const_node(&self.ast, id));
                        }
                        Some(vals)
                    } else {
                        None
                    };

                    let mut ctx = context!(self);
                    let alloca = self.builder.create(
                        &mut ctx,
                        ir::Op::new(
                            Type::Pointer {
                                base: Box::new(typ.clone()),
                            },
                            vec![
                                Attr::GlobalArray {
                                    name: name.clone(),
                                    mutable: true,
                                    typ: typ.clone(),
                                    values,
                                },
                                Attr::Name(name.clone()),
                            ],
                            OpData::GlobalAlloca(typ.size_in_bytes()),
                        ),
                    );
                    self.globals.insert(name, alloca);
                } else {
                    if self.current_function.is_some() && !self.has_active_insertion_point() {
                        return None;
                    }
                    let (dims, base) = match &typ {
                        Type::Array { dims, base } => (dims.clone(), *base.clone()),
                        _ => panic!("VarArray typ is not Array"),
                    };

                    let alloca = {
                        let mut ctx = context!(self);
                        self.builder.create(
                            &mut ctx,
                            ir::Op::new(
                                Type::Pointer {
                                    base: Box::new(typ.clone()),
                                },
                                vec![Attr::Name(name.clone())],
                                OpData::Alloca(typ.clone()),
                            ),
                        )
                    };
                    self.syms.insert(name, alloca.clone());

                    if let Some(init_ids) = init_values {
                        for (flat_idx, init_id) in init_ids.iter().enumerate() {
                            let value = emit_rval(self, *init_id);
                            let idxs = flat_to_indices(flat_idx, &dims);

                            let mut ctx =
                                context_or_err!(self, "Local array init outside function");
                            let addr = self.builder.create(
                                &mut ctx,
                                ir::Op::new(
                                    Type::Pointer {
                                        base: Box::new(base.clone()),
                                    },
                                    vec![],
                                    OpData::GEP {
                                        base: alloca.clone(),
                                        indices: std::iter::once(Operand::Int(0))
                                            .chain(
                                                idxs.into_iter()
                                                    .map(|idx| Operand::Int(idx as i32)),
                                            )
                                            .collect(),
                                    },
                                ),
                            );
                            self.builder.create(
                                &mut ctx,
                                ir::Op::new(Type::Void, vec![], OpData::Store { addr, value }),
                            );
                        }
                    }
                }
                None
            }
            Node::ConstArray {
                name,
                typ,
                init_values,
            } => {
                let typ = typ.clone();
                let init_values = init_values.clone();
                let emitted_name = if let Some(current_func) = self.current_function {
                    let func_name = self.program.funcs[current_func].name.clone();
                    let mangled_name = format!("__const_{}_{}_{}", func_name, name, self.counter);
                    self.counter += 1;
                    self.mangled.insert(name.clone(), mangled_name.clone());
                    mangled_name
                } else {
                    name.clone()
                };

                let values = if let Some(ids) = init_values {
                    let mut vals = vec![];
                    for id in ids {
                        vals.push(literal_from_const_node(&self.ast, id));
                    }
                    Some(vals)
                } else {
                    None
                };

                let mut ctx = context!(self);
                let alloca = self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Pointer {
                            base: Box::new(typ.clone()),
                        },
                        vec![
                            Attr::GlobalArray {
                                name: emitted_name.clone(),
                                mutable: false,
                                typ: typ.clone(),
                                values,
                            },
                            Attr::Name(emitted_name.clone()),
                        ],
                        OpData::GlobalAlloca(typ.size_in_bytes()),
                    ),
                );
                self.globals.insert(emitted_name, alloca);
                None
            }
            Node::Return(expr) => {
                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }
                let expr = *expr;
                let value = match expr {
                    Some(e) => Some(emit_rval(self, e)),
                    None => None,
                };
                self.insert_terminator_and_unplug(OpData::Ret { value });
                None
            }
            Node::If {
                condition,
                then_block,
                else_block,
            } => {
                let condition = *condition;
                let then_block = *then_block;
                let else_block = *else_block;

                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }

                if let Some(else_id) = else_block {
                    let (then_bb, else_bb) = {
                        let mut ctx = context_or_err!(self, "If statement outside function");
                        (
                            self.builder.create_new_block(&mut ctx),
                            self.builder.create_new_block(&mut ctx),
                        )
                    };

                    let cond = emit_rval(self, condition);
                    self.insert_terminator_if_needed(OpData::Br {
                        cond,
                        then_bb: then_bb.clone(),
                        else_bb: else_bb.clone(),
                    });

                    self.builder.set_current_block(then_bb.clone());
                    self.emit(then_block);
                    let then_fallthrough = self.builder.current_block.clone();

                    self.builder.set_current_block(else_bb.clone());
                    self.emit(else_id);
                    let else_fallthrough = self.builder.current_block.clone();

                    if then_fallthrough.is_some() || else_fallthrough.is_some() {
                        let end_bb = {
                            let mut ctx = context_or_err!(self, "If statement outside function");
                            self.builder.create_new_block(&mut ctx)
                        };

                        if let Some(bb) = then_fallthrough {
                            self.builder.set_current_block(bb);
                            self.insert_terminator_if_needed(OpData::Jump {
                                target_bb: end_bb.clone(),
                            });
                        }

                        if let Some(bb) = else_fallthrough {
                            self.builder.set_current_block(bb);
                            self.insert_terminator_if_needed(OpData::Jump {
                                target_bb: end_bb.clone(),
                            });
                        }

                        self.builder.set_current_block(end_bb);
                    } else {
                        self.builder.current_block = None;
                        self.builder.current_inst = None;
                    }
                } else {
                    let (then_bb, end_bb) = {
                        let mut ctx = context_or_err!(self, "If statement outside function");
                        (
                            self.builder.create_new_block(&mut ctx),
                            self.builder.create_new_block(&mut ctx),
                        )
                    };

                    let cond = emit_rval(self, condition);
                    self.insert_terminator_if_needed(OpData::Br {
                        cond,
                        then_bb: then_bb.clone(),
                        else_bb: end_bb.clone(),
                    });

                    self.builder.set_current_block(then_bb);
                    self.emit(then_block);
                    if self.has_active_insertion_point() {
                        self.insert_terminator_if_needed(OpData::Jump {
                            target_bb: end_bb.clone(),
                        });
                    }

                    self.builder.set_current_block(end_bb);
                }
                None
            }
            Node::While { condition, body } => {
                let condition = *condition;
                let body = *body;

                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }

                let (while_entry, while_body, while_end) = {
                    let mut ctx = context_or_err!(self, "While statement outside function");
                    let while_entry = self.builder.create_new_block(&mut ctx);
                    let while_body = self.builder.create_new_block(&mut ctx);
                    let while_end = self.builder.create_new_block(&mut ctx);

                    (while_entry, while_body, while_end)
                };

                self.insert_terminator_if_needed(OpData::Jump {
                    target_bb: while_entry.clone(),
                });

                self.builder.set_current_block(while_entry.clone());
                let cond = emit_rval(self, condition);
                self.insert_terminator_if_needed(OpData::Br {
                    cond,
                    then_bb: while_body.clone(),
                    else_bb: while_end.clone(),
                });

                self.builder.set_current_block(while_body);
                self.builder.push_loop(LoopInfo {
                    while_entry: Some(while_entry.clone()),
                    end_block: Some(while_end.clone()),
                });
                self.emit(body);
                self.builder.pop_loop();

                if self.has_active_insertion_point() {
                    self.insert_terminator_if_needed(OpData::Jump {
                        target_bb: while_entry,
                    });
                }

                self.builder.set_current_block(while_end);
                None
            }
            Node::Break => {
                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }
                let loop_info = self
                    .builder
                    .loop_stack
                    .last()
                    .unwrap_or_else(|| panic!("Break statement not inside a loop"));
                self.insert_terminator_and_unplug(OpData::Jump {
                    target_bb: loop_info.end_block.clone().unwrap(),
                });
                None
            }
            Node::Continue => {
                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }
                let loop_info = self
                    .builder
                    .loop_stack
                    .last()
                    .unwrap_or_else(|| panic!("Continue statement not inside a loop"));

                self.insert_terminator_and_unplug(OpData::Jump {
                    target_bb: loop_info.while_entry.clone().unwrap(),
                });
                None
            }
            Node::Assign { lhs, rhs } => {
                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }
                let lhs = *lhs;
                let rhs = *rhs;

                let rhs_op = emit_rval(self, rhs);
                let lhs_op = self
                    .emit(lhs)
                    .unwrap_or_else(|| panic!("Assignment lhs should be address expression"));

                let mut ctx = context_or_err!(self, "Store outside function");
                self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Void,
                        vec![],
                        OpData::Store {
                            addr: lhs_op,
                            value: rhs_op,
                        },
                    ),
                );
                None
            }
            Node::VarAccess { name, .. } => {
                if let Some(ptr_addr) = self.syms.get(name) {
                    Some(ptr_addr.clone())
                } else if let Some(global_id) = self.globals.get(name) {
                    Some(global_id.clone())
                } else {
                    panic!("VarAccess: variable {} not found in syms or globals", name)
                }
            }
            Node::ArrayAccess { name, indices, typ } => {
                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }
                let name = name.clone();
                let indices: Vec<NodeId> = indices.clone();
                let typ = typ.clone();

                let mut index_ops = vec![];
                for idx in indices {
                    index_ops.push(emit_rval(self, idx));
                }

                let mut ctx = context_or_err!(self, "Array access outside function");

                fn load_arr(
                    builder: &mut Builder,
                    ctx: &mut BuilderContext,
                    ptr: Operand,
                    indices: Vec<Operand>,
                    typ: Type,
                ) -> Operand {
                    let arr_typ = match ptr {
                        Operand::Value(id) => {
                            let dfg = ctx.dfg.as_ref().expect("DFG not found in context");
                            match dfg[id].typ.clone() {
                                Type::Pointer { base } => *base,
                                _ => panic!("Expected pointer type for array access"),
                            }
                        }
                        Operand::Global(id) => {
                            let globals = &ctx.globals;
                            match globals[id].typ.clone() {
                                Type::Pointer { base } => *base,
                                _ => panic!("Expected pointer type for array access"),
                            }
                        }
                        _ => panic!("Expected pointer operand for array access"),
                    };
                    match arr_typ {
                        Type::Array { .. } => {
                            // use GEP to reach the element directly
                            let ptr_typ = Type::Pointer {
                                base: Box::new(typ.clone()),
                            };
                            builder.create(
                                ctx,
                                ir::Op::new(
                                    ptr_typ,
                                    vec![],
                                    OpData::GEP {
                                        base: ptr.clone(),
                                        indices: std::iter::once(Operand::Int(0))
                                            .chain(indices)
                                            .collect(),
                                    },
                                ),
                            )
                        }
                        Type::Pointer { .. } => {
                            if !indices.is_empty() {
                                // Load the pointer first, then use GEP to reach the element
                                let loaded_ptr = builder.create(
                                    ctx,
                                    ir::Op::new(
                                        arr_typ,
                                        vec![],
                                        OpData::Load { addr: ptr.clone() },
                                    ),
                                );
                                let ptr_typ = Type::Pointer {
                                    base: Box::new(typ.clone()),
                                };
                                builder.create(
                                    ctx,
                                    ir::Op::new(
                                        ptr_typ,
                                        vec![],
                                        OpData::GEP {
                                            base: loaded_ptr,
                                            indices,
                                        },
                                    ),
                                )
                            } else {
                                ptr
                            }
                        }
                        _ => unreachable!("Expected array or pointer type for array access"),
                    }
                }

                let ptr_addr = if let Some(local_ptr) = self.syms.get(&name) {
                    load_arr(
                        &mut self.builder,
                        &mut ctx,
                        local_ptr.clone(),
                        index_ops,
                        typ,
                    )
                } else if let Some(mangled_name) = self.mangled.get(&name) {
                    let global_id = self.globals.get(mangled_name).unwrap_or_else(|| {
                        panic!(
                            "ArrayAccess: promoted const array {} not found in globals",
                            mangled_name
                        )
                    });
                    load_arr(
                        &mut self.builder,
                        &mut ctx,
                        global_id.clone(),
                        index_ops,
                        typ,
                    )
                } else if let Some(global_id) = self.globals.get(&name) {
                    load_arr(
                        &mut self.builder,
                        &mut ctx,
                        global_id.clone(),
                        index_ops,
                        typ,
                    )
                } else {
                    panic!("ArrayAccess: array {} not found in globals", name)
                };
                Some(ptr_addr)
            }
            Node::Call {
                typ,
                func_name,
                args,
            } => {
                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }
                let typ = typ.clone();
                let func_name = func_name.clone();
                let args: Vec<NodeId> = args.clone();

                let mut arg_ops = vec![];
                for arg in args {
                    arg_ops.push(emit_rval(self, arg));
                }

                let mut ctx = context_or_err!(self, "Call outside function");
                let call_op = self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        typ,
                        vec![Attr::FuncName(func_name.clone())],
                        OpData::Call {
                            func: Operand::Func(self.func_ids[&func_name]),
                            args: arg_ops,
                        },
                    ),
                );
                Some(call_op)
            }
            Node::BinaryOp { op, .. } => {
                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }
                let op = op.clone();

                let mut op_list: Vec<NodeId> = vec![];
                let origin = op.clone();
                let mut cur = node_id;
                // Collect the operations first
                while let Node::BinaryOp { lhs, op, .. } = &self.ast[cur] {
                    if *op == origin {
                        op_list.push(cur);
                        cur = *lhs;
                    } else {
                        break;
                    }
                }

                fn emit_code(
                    builder: &mut Builder,
                    ctx: &mut BuilderContext,
                    lhs: Operand,
                    rhs: Operand,
                    lhs_typ: Type,
                    rhs_typ: Type,
                    op: ast::Op,
                    typ: Type,
                ) -> Operand {
                    let op_data = match op {
                        ast::Op::Add => {
                            if typ == Type::Int {
                                OpData::AddI { lhs, rhs }
                            } else {
                                OpData::AddF { lhs, rhs }
                            }
                        }
                        ast::Op::Sub => {
                            if typ == Type::Int {
                                OpData::SubI { lhs, rhs }
                            } else {
                                OpData::SubF { lhs, rhs }
                            }
                        }
                        ast::Op::Mul => {
                            if typ == Type::Int {
                                OpData::MulI { lhs, rhs }
                            } else {
                                OpData::MulF { lhs, rhs }
                            }
                        }
                        ast::Op::Div => {
                            if typ == Type::Int {
                                OpData::DivI { lhs, rhs }
                            } else {
                                OpData::DivF { lhs, rhs }
                            }
                        }
                        ast::Op::Mod => {
                            if typ == Type::Int {
                                OpData::ModI { lhs, rhs }
                            } else {
                                panic!("Mod operator only supports Int type");
                            }
                        }
                        ast::Op::Eq => {
                            if typ == Type::Bool {
                                if lhs_typ == Type::Int && rhs_typ == Type::Int {
                                    OpData::SEq { lhs, rhs }
                                } else if lhs_typ == Type::Float && rhs_typ == Type::Float {
                                    OpData::OEq { lhs, rhs }
                                } else {
                                    panic!("Types of lhs and rhs must match for Eq operator: lhs is {:?}, rhs is {:?}", lhs_typ, rhs_typ);
                                }
                            } else {
                                panic!("Eq operator only returns Bool type");
                            }
                        }
                        ast::Op::Ne => {
                            if typ == Type::Bool {
                                if lhs_typ == Type::Int && rhs_typ == Type::Int {
                                    OpData::SNe { lhs, rhs }
                                } else if lhs_typ == Type::Float && rhs_typ == Type::Float {
                                    OpData::ONe { lhs, rhs }
                                } else {
                                    panic!("Types of lhs and rhs must match for Ne operator: lhs is {:?}, rhs is {:?}", lhs_typ, rhs_typ);
                                }
                            } else {
                                panic!("Ne operator only returns Bool type");
                            }
                        }
                        ast::Op::Gt => {
                            if typ == Type::Bool {
                                if lhs_typ == Type::Int && rhs_typ == Type::Int {
                                    OpData::SGt { lhs, rhs }
                                } else if lhs_typ == Type::Float && rhs_typ == Type::Float {
                                    OpData::OGt { lhs, rhs }
                                } else {
                                    panic!("Types of lhs and rhs must match for Gt operator: lhs is {:?}, rhs is {:?}", lhs_typ, rhs_typ);
                                }
                            } else {
                                panic!("Gt operator only returns Bool type");
                            }
                        }
                        ast::Op::Lt => {
                            if typ == Type::Bool {
                                if lhs_typ == Type::Int && rhs_typ == Type::Int {
                                    OpData::SLt { lhs, rhs }
                                } else if lhs_typ == Type::Float && rhs_typ == Type::Float {
                                    OpData::OLt { lhs, rhs }
                                } else {
                                    panic!("Types of lhs and rhs must match for Lt operator: lhs is {:?}, rhs is {:?}", lhs_typ, rhs_typ);
                                }
                            } else {
                                panic!("Lt operator only returns Bool type");
                            }
                        }
                        ast::Op::Ge => {
                            if typ == Type::Bool {
                                if lhs_typ == Type::Int && rhs_typ == Type::Int {
                                    OpData::SGe { lhs, rhs }
                                } else if lhs_typ == Type::Float && rhs_typ == Type::Float {
                                    OpData::OGe { lhs, rhs }
                                } else {
                                    panic!("Types of lhs and rhs must match for Ge operator: lhs is {:?}, rhs is {:?}", lhs_typ, rhs_typ);
                                }
                            } else {
                                panic!("Ge operator only returns Bool type");
                            }
                        }
                        ast::Op::Le => {
                            if typ == Type::Bool {
                                if lhs_typ == Type::Int && rhs_typ == Type::Int {
                                    OpData::SLe { lhs, rhs }
                                } else if lhs_typ == Type::Float && rhs_typ == Type::Float {
                                    OpData::OLe { lhs, rhs }
                                } else {
                                    panic!("Types of lhs and rhs must match for Le operator: lhs is {:?}, rhs is {:?}", lhs_typ, rhs_typ);
                                }
                            } else {
                                panic!("Le operator only returns Bool type");
                            }
                        }
                        ast::Op::And | ast::Op::Or => unreachable!("And/Or handled above"),
                        _ => panic!("Unsupported binary operator {:?} in Emit", op),
                    };

                    builder.create(ctx, ir::Op::new(typ, vec![], op_data))
                }

                let mut res = Operand::Value(0);
                for (idx, op_id) in op_list.iter().rev().enumerate() {
                    let (lhs, rhs, op_kind) = match &self.ast[*op_id] {
                        Node::BinaryOp { lhs, op, rhs, .. } => (*lhs, *rhs, op.clone()),
                        _ => panic!("Expected BinaryOp node, got {:?}", self.ast[*op_id]),
                    };

                    // Do short-circuit evaluation individually, since their emit behavior differ from normal op.
                    match op_kind {
                        ast::Op::And => {
                            let (result_alloca, rhs_block, end_block) = {
                                let mut ctx =
                                    context_or_err!(self, "BinaryOp And outside function");
                                let result_alloca = self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Pointer {
                                            base: Box::new(Type::Bool),
                                        },
                                        vec![Attr::Promotion],
                                        OpData::Alloca(Type::Bool),
                                    ),
                                );
                                self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Void,
                                        vec![],
                                        OpData::Store {
                                            addr: result_alloca.clone(),
                                            value: Operand::Bool(false),
                                        },
                                    ),
                                );
                                (
                                    result_alloca,
                                    self.builder.create_new_block(&mut ctx),
                                    self.builder.create_new_block(&mut ctx),
                                )
                            };

                            let lhs_op = if idx == 0 {
                                emit_rval(self, lhs)
                            } else {
                                // It's impossibe that res is not a Value operand,
                                // since the only way to get a non-Value operand is from a short-circuit op, which must be the first op in the list.
                                res
                            };
                            {
                                let mut ctx =
                                    context_or_err!(self, "BinaryOp And outside function");
                                self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Void,
                                        vec![],
                                        OpData::Br {
                                            cond: lhs_op,
                                            then_bb: rhs_block.clone(),
                                            else_bb: end_block.clone(),
                                        },
                                    ),
                                );
                            }

                            self.builder.set_current_block(rhs_block);
                            let rhs_op = emit_rval(self, rhs);
                            {
                                let mut ctx =
                                    context_or_err!(self, "BinaryOp And outside function");
                                self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Void,
                                        vec![],
                                        OpData::Store {
                                            addr: result_alloca.clone(),
                                            value: rhs_op,
                                        },
                                    ),
                                );
                                self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Void,
                                        vec![],
                                        OpData::Jump {
                                            target_bb: end_block.clone(),
                                        },
                                    ),
                                );
                            }

                            self.builder.set_current_block(end_block);
                            let mut ctx = context_or_err!(self, "BinaryOp And outside function");
                            let load_result = self.builder.create(
                                &mut ctx,
                                ir::Op::new(
                                    Type::Bool,
                                    vec![],
                                    OpData::Load {
                                        addr: result_alloca,
                                    },
                                ),
                            );
                            res = load_result;
                            continue;
                        }
                        ast::Op::Or => {
                            let (result_alloca, rhs_block, end_block) = {
                                let mut ctx = context_or_err!(self, "BinaryOp Or outside function");
                                let result_alloca = self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Pointer {
                                            base: Box::new(Type::Bool),
                                        },
                                        vec![Attr::Promotion],
                                        OpData::Alloca(Type::Bool),
                                    ),
                                );
                                self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Void,
                                        vec![],
                                        OpData::Store {
                                            addr: result_alloca.clone(),
                                            value: Operand::Bool(true),
                                        },
                                    ),
                                );
                                (
                                    result_alloca,
                                    self.builder.create_new_block(&mut ctx),
                                    self.builder.create_new_block(&mut ctx),
                                )
                            };

                            let lhs_op = if idx == 0 { emit_rval(self, lhs) } else { res };
                            {
                                let mut ctx = context_or_err!(self, "BinaryOp Or outside function");
                                self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Void,
                                        vec![],
                                        OpData::Br {
                                            cond: lhs_op,
                                            then_bb: end_block.clone(),
                                            else_bb: rhs_block.clone(),
                                        },
                                    ),
                                );
                            }

                            self.builder.set_current_block(rhs_block);
                            let rhs_op = emit_rval(self, rhs);
                            {
                                let mut ctx = context_or_err!(self, "BinaryOp Or outside function");
                                self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Void,
                                        vec![],
                                        OpData::Store {
                                            addr: result_alloca.clone(),
                                            value: rhs_op,
                                        },
                                    ),
                                );
                                self.builder.create(
                                    &mut ctx,
                                    ir::Op::new(
                                        Type::Void,
                                        vec![],
                                        OpData::Jump {
                                            target_bb: end_block.clone(),
                                        },
                                    ),
                                );
                            }

                            self.builder.set_current_block(end_block);
                            let mut ctx = context_or_err!(self, "BinaryOp Or outside function");
                            let load_result = self.builder.create(
                                &mut ctx,
                                ir::Op::new(
                                    Type::Bool,
                                    vec![],
                                    OpData::Load {
                                        addr: result_alloca,
                                    },
                                ),
                            );
                            res = load_result;
                            continue;
                        }
                        _ => {}
                    }

                    let mut lhs_op = if idx == 0 {
                        emit_rval(self, lhs)
                    } else {
                        // It's impossibe that res is not a Value operand,
                        // since the only way to get a non-Value operand is from a short-circuit op, which must be the first op in the list.
                        res
                    };
                    let expected_lhs_typ = node_value_type(&self.ast, lhs);
                    let actual_lhs_typ = self.get_type(&lhs_op);
                    if actual_lhs_typ != expected_lhs_typ {
                        lhs_op = emit_cast(self, lhs_op, actual_lhs_typ, expected_lhs_typ);
                    }
                    let rhs_op = emit_rval(self, rhs);
                    let lhs_typ = self.get_type(&lhs_op);
                    let rhs_typ = self.get_type(&rhs_op);
                    let new_op_id = emit_code(
                        &mut self.builder,
                        &mut context_or_err!(self, "BinaryOp outside function"),
                        lhs_op,
                        rhs_op,
                        lhs_typ,
                        rhs_typ,
                        op_kind,
                        match &self.ast[*op_id] {
                            Node::BinaryOp { typ, .. } => typ.clone(),
                            _ => panic!("Expected BinaryOp node, got {:?}", self.ast[*op_id]),
                        },
                    );
                    res = new_op_id;
                }
                Some(res)
            }
            Node::UnaryOp { typ, op, operand } => {
                if self.current_function.is_some() && !self.has_active_insertion_point() {
                    return None;
                }
                let typ = typ.clone();
                let op = op.clone();
                let operand = *operand;

                let operand_op = emit_rval(self, operand);
                let mut ctx = context_or_err!(self, "UnaryOp outside function");

                let op_data = match op {
                    ast::Op::Plus => {
                        return Some(operand_op);
                    }
                    ast::Op::Minus => {
                        if typ == Type::Int {
                            OpData::SubI {
                                lhs: Operand::Int(0),
                                rhs: operand_op,
                            }
                        } else {
                            OpData::SubF {
                                lhs: Operand::Float(0.0),
                                rhs: operand_op,
                            }
                        }
                    }
                    ast::Op::Not => {
                        if typ == Type::Bool {
                            OpData::Xor {
                                lhs: operand_op,
                                rhs: Operand::Bool(true),
                            }
                        } else {
                            panic!(
                                "Not operator only supports Bool type: {:?}",
                                self.ast[node_id]
                            );
                        }
                    }
                    ast::Op::Bool2Int => OpData::Zext { value: operand_op },
                    ast::Op::Int2Bool => OpData::SNe {
                        lhs: operand_op,
                        rhs: Operand::Int(0),
                    },
                    ast::Op::Float2Int => OpData::Fptosi { value: operand_op },
                    ast::Op::Int2Float => OpData::Sitofp { value: operand_op },
                    ast::Op::Bool2Float => OpData::Uitofp { value: operand_op },
                    ast::Op::Float2Bool => OpData::ONe {
                        lhs: operand_op,
                        rhs: Operand::Float(0.0),
                    },
                    _ => {
                        panic!(
                            "Unsupported unary operator in Emit: {:?}",
                            self.ast[node_id]
                        );
                    }
                };

                let un_op = self
                    .builder
                    .create(&mut ctx, ir::Op::new(typ, vec![], op_data));
                Some(un_op)
            }
            Node::Literal(Literal::Int(val)) => Some(Operand::Int(*val)),
            Node::Literal(Literal::Float(val)) => Some(Operand::Float(*val)),
            Node::Literal(Literal::String(string)) => {
                let string = string.clone();
                self.str_counter += 1;

                let typ = Type::Array {
                    base: Box::new(Type::Char),
                    dims: vec![(string.len() + 1) as u32],
                };

                let mut ctx = context!(self);
                let global_alloca = self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        Type::Pointer {
                            base: Box::new(typ.clone()),
                        },
                        vec![Attr::GlobalArray {
                            name: "".to_string(),
                            typ: typ.clone(),
                            mutable: false,
                            values: Some(
                                string
                                    .chars()
                                    .map(|c| Literal::Int(c as i32))
                                    .chain(std::iter::once(Literal::Int(0)))
                                    .collect(),
                            ),
                        }],
                        OpData::GlobalAlloca(typ.size_in_bytes()),
                    ),
                );
                let ptr_typ = decay(typ).unwrap_or_else(|e| panic!("{}", e));
                let ptr_addr = self.builder.create(
                    &mut ctx,
                    ir::Op::new(
                        ptr_typ,
                        vec![],
                        OpData::GEP {
                            base: global_alloca,
                            indices: vec![Operand::Int(0), Operand::Int(0)],
                        },
                    ),
                );
                Some(ptr_addr)
            }
            _ => None,
        }
    }
}

impl Pass<Program> for Emit {
    fn run(&mut self) -> Program {
        SYSY_LIB.with(|lib| {
            let mut ctx = context!(self);
            for (name, typ) in lib.iter() {
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
                );
            }
            for (name, typ) in lib.iter() {
                let func_id =
                    self.program
                        .funcs
                        .add(Function::new(name.to_string(), true, typ.clone()));
                self.func_ids.insert(name.to_string(), func_id);
            }
        });

        let root = self
            .ast
            .entry
            .unwrap_or_else(|| panic!("Emit: AST entry is missing"));
        self.emit(root);

        std::mem::take(&mut self.program)
    }
}
