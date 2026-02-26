use crate::base::ir::{OpData, Operand, PhiIncoming};
/**
 * Dead Code Elimination (DCE).
 */
use crate::base::{context_or_err, Pass};
use crate::base::{Builder, BuilderContext};

pub struct DCE<'a> {
    pub program: &'a mut crate::base::ir::Program,
    builder: Builder,
    // Worklist of inst
    worklist: Vec<(Operand, Operand)>,
    // State fields
    current_function: Option<usize>,
}

impl<'a> DCE<'a> {
    pub fn new(program: &'a mut crate::base::ir::Program) -> Self {
        Self {
            program,
            builder: Builder::new(),
            worklist: vec![],
            current_function: None,
        }
    }

    pub fn is_dead(&self, operand: &Operand) -> bool {
        let current_func = match self.current_function {
            Some(idx) => &self.program.funcs[idx],
            None => panic!("DCE: not in a function"),
        };
        let dfg = &current_func.dfg;
        let globals = &self.program.globals;
        match operand {
            Operand::Value(id) => dfg[*id].users.is_empty(),
            Operand::Global(id) => globals[*id].users.is_empty(),
            _ => panic!("DCE: operand is not a value"),
        }
    }

    pub fn init(&mut self, func_id: usize) {
        self.current_function = Some(func_id);
        let func = &self.program.funcs[self.current_function.unwrap()];
        // Initialize the worklist
        for block_id in func.cfg.collect() {
            let block = &func.cfg[block_id];
            for inst_id in block.cur.iter() {
                let op_id = match inst_id {
                    Operand::Value(id) => *id,
                    _ => panic!("DCE: instruction id is not a value"),
                };
                let inst = &func.dfg[op_id];
                if self.is_dead(inst_id) && !inst.is_impure() {
                    self.worklist.push((inst_id.clone(), Operand::BB(block_id)));
                }
            }
        }
    }

    fn run(&mut self) {
        fn check(this: &mut DCE, operand: &Operand, bb_id: &Operand) {
            let func = match this.current_function {
                Some(idx) => &this.program.funcs[idx],
                None => panic!("DCE: not in a function"),
            };
            match operand {
                Operand::Value(id) => {
                    let op_id = *id;
                    if this.is_dead(operand) && !func.dfg[op_id].is_impure() {
                        this.worklist.push((operand.clone(), bb_id.clone()));
                    }
                }
                Operand::Global(id) => {
                    let global_id = *id;
                    if this.is_dead(operand) && !this.program.globals[global_id].is_impure() {
                        this.worklist.push((operand.clone(), bb_id.clone()));
                    }
                }
                Operand::Int(_)
                | Operand::Float(_)
                | Operand::Undefined
                | Operand::Index(_)
                | Operand::Param { .. } => { /* do nothing */ }
                _ => panic!("DCE: operand is not a value or basic block: {:?}", operand),
            }
        }
        for func_id in self.program.funcs.collect_internal() {
            self.init(func_id);
            while let Some((op_id, bb_id)) = self.worklist.pop() {
                let mut ctx = context_or_err!(self, "DCE: no context in run");
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
                    | OpData::And { lhs, rhs }
                    | OpData::Or { lhs, rhs }
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
                        check(self, &lhs, &bb_id);
                        check(self, &rhs, &bb_id);
                    }
                    OpData::Sitofp { value }
                    | OpData::Fptosi { value }
                    | OpData::Zext { value }
                    | OpData::Uitofp { value } => {
                        check(self, &value, &bb_id);
                    }
                    // In DCE, Load is pure.
                    OpData::Load { addr } => {
                        check(self, &addr, &bb_id);
                    }
                    OpData::GEP { base, indices } => {
                        check(self, &base, &bb_id);
                        for index in indices.iter() {
                            check(self, index, &bb_id);
                        }
                    }

                    OpData::Phi { incoming } => {
                        for phi_incoming in incoming.iter() {
                            if let PhiIncoming::Data { value, bb } = phi_incoming {
                                check(self, value, bb);
                            }
                        }
                    }

                    OpData::Call { .. }
                    | OpData::Store { .. }
                    | OpData::Br { .. }
                    | OpData::Jump { .. }
                    | OpData::Ret { .. }
                    | OpData::Move { .. }
                    | OpData::Alloca(_)
                    | OpData::GlobalAlloca(_)
                    | OpData::Declare { .. } => {
                        unreachable!("DCE: impure instruction should not be in the worklist")
                    }
                }
            }
        }
    }
}

impl Pass<()> for DCE<'_> {
    fn run(&mut self) {
        self.run()
    }
}
