/// Simplify CFG.
use crate::base::ir::{OpData, OpType, Operand, Program};
use crate::base::{context_or_err, Builder, BuilderContext, Pass, Type};
use crate::utils::bitset::BitSet;

pub struct SimplifyCFG<'a> {
    pub program: &'a mut Program,
    builder: Builder,
    visited: BitSet,
    current_function: Option<usize>,
}

impl<'a> SimplifyCFG<'a> {
    pub fn new(program: &'a mut Program) -> Self {
        Self {
            program,
            builder: Builder::new(),
            visited: BitSet::new(),
            current_function: None,
        }
    }

    pub fn init(&mut self, idx: usize) {
        self.current_function = Some(idx);
        self.visited.clear();
    }

    // This function is invoked only if the current block has merely one instruction(The terminator).
    fn elim(&mut self, bb_id: Operand) {
        let cfg = &self.program.funcs[self.current_function.unwrap()].cfg;
        let bb = &cfg[bb_id.clone()];
        if !bb.cur.len() == 1 {
            panic!("SimplifyCFG: The current block should have only one instruction");
        }
        if !bb.succs.len() == 1 {
            panic!("SimplifyCFG: The current block should have only one successor");
        }
        let succ_id = bb.succs[0].clone();

        for pred_id in bb.preds.clone() {
            let pred = &cfg[bb.preds[0].clone()];
            let pred_last_id = match pred.cur.last() {
                Some(inst_id) => inst_id.clone(),
                None => panic!("SimplifyCFG: The predecessor block should not be empty"),
            };

            let updated_pred_last_op = {
                let dfg = &self.program.funcs[self.current_function.unwrap()].dfg;
                let mut pred_last_op = dfg[pred_last_id.clone()].clone();
                // Replace the target block of the predecessor's terminator with the successor block.
                match &mut pred_last_op.data {
                    OpData::Jump { target_bb } => {
                        if *target_bb == bb_id {
                            *target_bb = succ_id.clone();
                        } else {
                            panic!(
                            "SimplifyCFG: The predecessor block should jump to the current block"
                        );
                        }
                    }
                    OpData::Br {
                        then_bb, else_bb, ..
                    } => {
                        if *then_bb == bb_id {
                            *then_bb = succ_id.clone();
                        } else if *else_bb == bb_id {
                            *else_bb = succ_id.clone();
                        } else {
                            panic!(
                            "SimplifyCFG: The predecessor block should branch to the current block"
                        );
                        }
                    }
                    OpData::AddF { .. }
                    | OpData::SubF { .. }
                    | OpData::MulF { .. }
                    | OpData::DivF { .. }
                    | OpData::AddI { .. }
                    | OpData::SubI { .. }
                    | OpData::MulI { .. }
                    | OpData::DivI { .. }
                    | OpData::ModI { .. }
                    | OpData::SNe { .. }
                    | OpData::SEq { .. }
                    | OpData::SGt { .. }
                    | OpData::SLt { .. }
                    | OpData::SGe { .. }
                    | OpData::SLe { .. }
                    | OpData::OEq { .. }
                    | OpData::OGt { .. }
                    | OpData::OLt { .. }
                    | OpData::OGe { .. }
                    | OpData::OLe { .. }
                    | OpData::ONe { .. }
                    | OpData::And { .. }
                    | OpData::Or { .. }
                    | OpData::Xor { .. }
                    | OpData::Shl { .. }
                    | OpData::Shr { .. }
                    | OpData::Sar { .. }
                    | OpData::Sitofp { .. }
                    | OpData::Fptosi { .. }
                    | OpData::Zext { .. }
                    | OpData::Uitofp { .. }
                    | OpData::Store { .. }
                    | OpData::Ret { .. }
                    | OpData::GEP { .. }
                    | OpData::Load { .. }
                    | OpData::Call { .. }
                    | OpData::Phi { .. }
                    | OpData::Move { .. }
                    | OpData::Alloca(_)
                    | OpData::GlobalAlloca(_)
                    | OpData::Declare { .. } => panic!(
                "SimplifyCFG: The predecessor block should end with a jump or branch instruction"
            ),
                }
                pred_last_op
            };
            // Replace the old terminator with the new one.
            self.builder.replace_op(
                &mut context_or_err!(self, "SimplifyCFG: No current function context found"),
                pred_last_id.clone(),
                pred_id.clone(),
                updated_pred_last_op,
            );
        }
    }

    pub fn simplify(&mut self, bb_id: usize) {
        if self.visited.contains(bb_id) {
            return;
        }
        self.visited.insert(bb_id);

        if {
            let bb = &self.program.funcs[self.current_function.unwrap()].cfg[bb_id];
            // We now ignore those
            bb.preds.len() == 1 && bb.succs.len() == 1 
        } {
            let bb = &self.program.funcs[self.current_function.unwrap()].cfg[bb_id];
            // Move the instructions in bb to its successor.
            let pred_id = bb.preds[0].clone();
            let pred = &self.program.funcs[self.current_function.unwrap()].cfg[pred_id.clone()];
            if pred.succs.len() == 1 && pred.succs[0] == Operand::BB(bb_id) {
                // Then merge current block into its predecessor.
                let mut ctx =
                    context_or_err!(self, "SimplifyCFG: No current function context found");
                let pred_last = match pred.cur.last() {
                    Some(inst_id) => inst_id.clone(),
                    None => panic!("SimplifyCFG: The predecessor block should not be empty"),
                };
                // Move the instructions, except the terminator.
                // It's impossible that the current block has any phi instruction.
                for inst_id in bb.cur.iter().skip(bb.cur.len() - 1) {
                    self.builder.move_op_to_bb_at(
                        &mut ctx,
                        inst_id.clone(),
                        Operand::BB(bb_id),
                        pred_id.clone(),
                        Some(pred_last.clone()),
                    );
                }
            } else {
                // Else move the instructions in current block to its successor.
                let mut ctx =
                    context_or_err!(self, "SimplifyCFG: No current function context found");
                let succ_non_phi_pos = bb
                    .cur
                    .iter()
                    .position(|inst_id| {
                        let dfg = ctx.dfg.as_ref().unwrap();
                        !dfg[inst_id.clone()].is(OpType::Phi)
                    })
                    .unwrap_or(0);
                for inst_id in bb.cur.iter().rev().skip(1) {
                    self.builder.move_op_to_bb_at(
                        &mut ctx,
                        inst_id.clone(),
                        Operand::BB(bb_id),
                        bb.succs[0].clone(),
                        Some(bb.cur[succ_non_phi_pos].clone()),
                    );
                }
            }
            self.elim(Operand::BB(bb_id));
        } else if {
            let bb = &self.program.funcs[self.current_function.unwrap()].cfg[bb_id];
            let dfg = &self.program.funcs[self.current_function.unwrap()].dfg;
            bb.cur.len() == 1 && dfg[bb.cur[0].clone()].is(OpType::Jump)
        } {
            self.elim(Operand::BB(bb_id));
        }

        let bb = &self.program.funcs[self.current_function.unwrap()].cfg[bb_id];
        if !bb.succs.is_empty() {
            for succ_id in bb.succs.clone() {
                self.simplify(succ_id.get_bb_id());
            }
        } else {
            // Check return statement.
            let dfg = &self.program.funcs[self.current_function.unwrap()].dfg;
            if bb.cur.is_empty() {
                panic!("SimplifyCFG: The block should not be empty");
            }

            let last = bb.cur.last().unwrap();
            let op = &dfg[last.clone()];
            if !op.is(OpType::Ret) {
                panic!("SimplifyCFG: The last instruction of a block without successor should be a return instruction");
            }

            let func_ret_typ = match &self.program.funcs[self.current_function.unwrap()].typ {
                Type::Function { return_type, .. } => (**return_type).clone(),
                _ => panic!("SimplifyCFG: The current function should have a function type"),
            };
            if op.typ != func_ret_typ {
                panic!("SimplifyCFG: The return type of the return instruction should match the function return type");
            }
        }
    }

    pub fn rewrite(&mut self) {
        
    }

    pub fn run(&mut self) {
        // We can only simplify CFG at the end of all other optimizations, since it may change the structure of CFG and thus invalidate the assumptions of other optimizations.
        for func_id in self.program.funcs.collect_internal() {
            self.init(func_id);
            let entry = match self.program.funcs[func_id].cfg.entry {
                Some(entry) => entry,
                None => continue,
            };
            self.simplify(entry);
        }
    }
}

impl Pass<()> for SimplifyCFG<'_> {
    fn run(&mut self) -> () {
        self.run();
    }
}
