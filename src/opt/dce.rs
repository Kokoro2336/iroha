/// Dead Code Elimination (DCE).
use crate::base::{Builder, Pass};
use crate::ir::mir::{OpData, Operand, PhiIncoming, Program};
use crate::utils::context::context_or_err;
use crate::utils::arena::ArenaItem;

#[allow(clippy::upper_case_acronyms)]
pub struct DCE<'a> {
    pub program: Option<&'a mut Program>,
    builder: Builder,
    // Worklist of inst
    worklist: Vec<(Operand, Operand)>,
    // Mapping from op_id to bb_id
    op_to_bb: Vec<Operand>,
    // State fields
    current_function: Option<usize>,
}

impl<'a> DCE<'a> {
    pub fn new() -> Self {
        Self {
            program: None,
            builder: Builder::new(),
            worklist: vec![],
            op_to_bb: vec![],
            current_function: None,
        }
    }

    pub fn is_dead(&self, operand: &Operand) -> bool {
        let program = self.program.as_ref().unwrap();
        let current_func = match self.current_function {
            Some(idx) => &program.funcs[idx],
            None => panic!("DCE: not in a function"),
        };
        let dfg = &current_func.dfg;
        let globals = &program.globals;
        match operand {
            Operand::Value(id) => dfg[*id].users.is_empty(),
            Operand::Global(id) => globals[*id].users.is_empty(),
            _ => panic!("DCE: operand is not a value"),
        }
    }

    pub fn init(&mut self, func_id: usize) {
        self.current_function = Some(func_id);
        let program = self.program.as_ref().unwrap();
        let func = &program.funcs[self.current_function.unwrap()];
        self.worklist.clear();

        // map OpId to BBId
        self.op_to_bb.clear();
        self.op_to_bb.resize(func.dfg.storage.len(), Operand::BB(0));
        func.cfg
            .storage
            .iter()
            .enumerate()
            .for_each(|(bb_id, item)| {
                if let ArenaItem::Data(bb) = item {
                    for op_id in bb.cur.iter() {
                        self.op_to_bb[op_id.get_op_id()] = Operand::BB(bb_id);
                    }
                }
            });

        // Initialize the worklist
        for block_id in func.cfg.collect() {
            let block = &func.cfg[block_id];
            for inst_id in block.cur.iter() {
                let op_id = match inst_id {
                    Operand::Value(id) => *id,
                    _ => panic!("DCE: instruction id is not a value"),
                };
                let is_impure = {
                    let inst = &func.dfg[op_id];
                    inst.is_impure()
                };
                if self.is_dead(inst_id) && !is_impure {
                    self.worklist.push((inst_id.clone(), Operand::BB(block_id)));
                }
            }
        }
    }
}

impl<'a> Pass<'a> for DCE<'a> {
    fn name(&self) -> &str {
        "DCE"
    }
    fn set_program(&mut self, program: &'a mut crate::ir::mir::Program) {
        self.program = Some(program);
    }
    fn run(&mut self) {
        fn check(this: &mut DCE, operand: &Operand) {
            let program = this.program.as_ref().unwrap();
            let func = match this.current_function {
                Some(idx) => &program.funcs[idx],
                None => panic!("DCE: not in a function"),
            };
            match operand {
                Operand::Value(id) => {
                    let op_id = *id;
                    if this.is_dead(operand) && !func.dfg[op_id].is_impure() {
                        this.worklist
                            .push((operand.clone(), this.op_to_bb[op_id].clone()));
                    }
                }
                Operand::Global(id) => {
                    let global_id = *id;
                    if this.is_dead(operand) && !program.globals[global_id].is_impure() {
                        this.worklist.push((operand.clone(), Operand::BB(0)));
                    }
                }
                Operand::Int(_)
                | Operand::Float(_)
                | Operand::Undefined
                | Operand::Param { .. } => { /* do nothing */ }
                _ => panic!("DCE: operand is not a value or basic block: {:?}", operand),
            }
        }
        let func_ids = self.program.as_ref().unwrap().funcs.collect_internal();
        for func_id in func_ids {
            self.init(func_id);
            while let Some((op_id, bb_id)) = self.worklist.pop() {
                if let Operand::Value(id) = op_id {
                    let func =
                        &self.program.as_ref().unwrap().funcs[self.current_function.unwrap()];
                    let bb = bb_id.get_bb_id();
                    if !func.cfg[bb].cur.iter().any(|inst| inst.get_op_id() == id) {
                        continue;
                    }
                }

                let mut ctx = context_or_err(
                    self.program.as_deref_mut().unwrap(),
                    self.current_function,
                    "DCE: no context in run",
                );
                self.builder.set_current_block(bb_id.clone());
                let removed_op = match op_id {
                    Operand::Global(_) => self.builder.remove_op(&mut ctx, op_id, None),
                    _ => self
                        .builder
                        .remove_op(&mut ctx, op_id.clone(), Some(bb_id.clone())),
                };

                // Check the operands of the removed instruction
                match removed_op.data.clone() {
                    OpData::AddF { lhs, rhs }
                    | OpData::SubF { lhs, rhs }
                    | OpData::MulF { lhs, rhs }
                    | OpData::DivF { lhs, rhs }
                    | OpData::AddI { lhs, rhs }
                    | OpData::SubI { lhs, rhs }
                    | OpData::MulI { lhs, rhs }
                    | OpData::DivI { lhs, rhs }
                    | OpData::ModI { lhs, rhs }
                    | OpData::SNe { lhs, rhs }
                    | OpData::SEq { lhs, rhs }
                    | OpData::SGt { lhs, rhs }
                    | OpData::SLt { lhs, rhs }
                    | OpData::SGe { lhs, rhs }
                    | OpData::SLe { lhs, rhs }
                    | OpData::Xor { lhs, rhs }
                    | OpData::Shl { lhs, rhs }
                    | OpData::Shr { lhs, rhs }
                    | OpData::Sar { lhs, rhs }
                    | OpData::ONe { lhs, rhs }
                    | OpData::OEq { lhs, rhs }
                    | OpData::OGt { lhs, rhs }
                    | OpData::OLt { lhs, rhs }
                    | OpData::OGe { lhs, rhs }
                    | OpData::OLe { lhs, rhs } => {
                        check(self, &lhs);
                        check(self, &rhs);
                    }
                    OpData::Sitofp { value }
                    | OpData::Fptosi { value }
                    | OpData::Zext { value }
                    | OpData::Uitofp { value } => {
                        check(self, &value);
                    }
                    // In DCE, Load is pure.
                    OpData::Load { addr } => {
                        check(self, &addr);
                    }
                    OpData::GEP { base, indices } => {
                        check(self, &base);
                        for index in indices.iter() {
                            check(self, index);
                        }
                    }

                    OpData::Phi { incoming } => {
                        for phi_incoming in incoming.iter() {
                            if let PhiIncoming::Data { value, bb: _ } = phi_incoming {
                                check(self, value);
                            }
                        }
                    }

                    OpData::Call { .. }
                    | OpData::Store { .. }
                    | OpData::Br { .. }
                    | OpData::Jump { .. }
                    | OpData::Ret { .. }
                    | OpData::Alloca(_)
                    | OpData::GlobalAlloca(_)
                    | OpData::Declare { .. } => {
                        unreachable!(
                            "DCE: impure instruction should not be in the worklist: {:?}",
                            removed_op
                        );
                    }
                }
            }
        }
    }
}
