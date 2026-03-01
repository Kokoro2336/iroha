use crate::base::ir::{Attr, OpData, Operand, PhiIncoming, Program};
use crate::base::{context_or_err, Builder, BuilderContext, Pass};

enum CheckType {
    Empty,           // No non-phi incoming value. We can replace the phi with undef.
    Single(Operand), // The single non-phi incoming value. We can replace the phi with this value.
    Ignore,          // Multiple or non-phi
}

pub struct RemoveTrivialPhi<'a> {
    program: &'a mut Program,
    builder: Builder,
    phi_ids: Vec<Vec<(Operand, Operand)>>,

    // Ancillary state fields
    worklist: Vec<(Operand, Operand, CheckType)>, // Vec of (PhiId, BBId, CheckType)

    // State function
    current_function: Option<usize>,
}

impl<'a> RemoveTrivialPhi<'a> {
    pub fn new(program: &'a mut Program, phi_ids: Vec<Vec<(Operand, Operand)>>) -> Self {
        Self {
            program,
            builder: Builder::new(),
            phi_ids,
            current_function: None,
            worklist: Vec::new(),
        }
    }

    fn check(ctx: &mut BuilderContext, phi: Operand) -> CheckType {
        let dfg = ctx.dfg.as_ref().unwrap();
        let phi_op = &dfg[phi.clone()];
        match &phi_op.data {
            OpData::Phi { incoming } => {
                let mut distinct: Vec<(Operand, Operand)> = vec![];
                for phi_incoming in incoming.iter() {
                    let (value, bb_id) = match phi_incoming {
                        PhiIncoming::Data { value, bb } => (value, bb),
                        PhiIncoming::None => continue,
                    };
                    if matches!(value, Operand::Undefined) || *value == phi {
                        continue;
                    }

                    if distinct.iter().all(|(v, _)| *v != *value) {
                        distinct.push((value.clone(), bb_id.clone()));
                        if distinct.len() > 1 {
                            return CheckType::Ignore;
                        }
                    }
                }

                if distinct.is_empty() {
                    CheckType::Empty
                } else {
                    let (value, _) = distinct.pop().unwrap();
                    CheckType::Single(value)
                }
            }
            // If it's not a phi, we treat it as multiple to be safe, since we only want to remove trivial phis.
            _ => CheckType::Ignore,
        }
    }

    fn init(&mut self, idx: usize) {
        self.current_function = Some(idx);
        self.worklist = self.phi_ids[idx]
            .iter()
            .map(|(phi_id, bb_id)| {
                let mut ctx =
                    context_or_err!(self, "RemoveTrivialPhi: No current function context found");
                let check_result = Self::check(&mut ctx, phi_id.clone());
                (phi_id.clone(), bb_id.clone(), check_result)
            })
            .collect();
    }

    fn remove_phi(&mut self) {
        let idx = match self.current_function {
            Some(i) => i,
            None => panic!("RemoveTrivialPhi: no current function"),
        };
        // Check whether the phi_ids are valid
        while let Some((phi_id, bb_id, check_result)) = self.worklist.pop() {
            let uses = {
                let func_id = match self.current_function {
                    Some(id) => id,
                    None => panic!("RemoveTrivialPhi: no current function"),
                };
                let func = &mut self.program.funcs[func_id];
                let phi_op = &mut func.dfg[phi_id.clone()];
                // Remove OldIdx Attr
                phi_op.attrs.retain(|attr| !matches!(attr, Attr::OldIdx(_)));
                phi_op.users.clone()
            };
            let mut ctx =
                context_or_err!(self, "RemoveTrivialPhi: No current function context found");
            match check_result {
                CheckType::Empty => {
                    crate::debug::info!("Remove trivial phi {:?} with undef", phi_id);
                    self.builder
                        .replace_all_uses(&mut ctx, phi_id.clone(), Operand::Undefined);
                    for user in uses {
                        // Ignore phi itself, since it will be removed later and should not pushed to worklist again.
                        if user == phi_id {
                            continue;
                        }
                        let check_result = Self::check(&mut ctx, user.clone());
                        if matches!(check_result, CheckType::Empty | CheckType::Single(_)) {
                            if let Some((id, bb)) = self.phi_ids[idx]
                                .iter()
                                .find(|(id, _)| *id == user)
                                .map(|(id, bb)| (id.clone(), bb.clone()))
                            {
                                // We should check whether the user phi is already in the worklist to avoid duplicate entries.
                                if !self.worklist.iter().any(|(w_id, _, _)| *w_id == id) {
                                    self.worklist.push((id.clone(), bb.clone(), check_result));
                                }
                            }
                        }
                    }
                    self.builder.set_current_block(bb_id.clone());
                    self.builder.remove_op(&mut ctx, phi_id, Some(bb_id));
                }
                CheckType::Single(value) => {
                    crate::debug::info!("Remove trivial phi {:?} with value {:?}", phi_id, value);
                    self.builder
                        .replace_all_uses(&mut ctx, phi_id.clone(), value);
                    for user in uses {
                        if user == phi_id {
                            continue;
                        }
                        let check_result = Self::check(&mut ctx, user.clone());
                        if matches!(check_result, CheckType::Empty | CheckType::Single(_)) {
                            if let Some((id, bb)) = self.phi_ids[idx]
                                .iter()
                                .find(|(id, _)| *id == user)
                                .map(|(id, bb)| (id.clone(), bb.clone()))
                            {
                                // We should check whether the user phi is already in the worklist to avoid duplicate entries.
                                if !self.worklist.iter().any(|(w_id, _, _)| *w_id == id) {
                                    self.worklist.push((id.clone(), bb.clone(), check_result));
                                }
                            }
                        }
                    }
                    self.builder.set_current_block(bb_id.clone());
                    self.builder.remove_op(&mut ctx, phi_id, Some(bb_id));
                }
                CheckType::Ignore => {}
            }
        }
    }

    pub fn run(&mut self) {
        for idx in self.program.funcs.collect_internal() {
            self.init(idx);
            self.remove_phi();
        }
    }
}

impl<'a> Pass<()> for RemoveTrivialPhi<'a> {
    fn run(&mut self) {
        self.run();
    }
}
