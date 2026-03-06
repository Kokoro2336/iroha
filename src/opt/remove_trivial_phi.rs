/// Remove Trivial Phi.
use crate::base::{Builder, BuilderContext, Pass};
use crate::ir::mir::{Attr, OpData, OpType, Operand, PhiIncoming, Program};
use crate::utils::context::context_or_err;
use crate::utils::arena::ArenaItem;

enum CheckType {
    Empty,           // No non-phi incoming value. We can replace the phi with undef.
    Single(Operand), // The single non-phi incoming value. We can replace the phi with this value.
    Ignore,          // Multiple or non-phi
}

pub struct RemoveTrivialPhi<'a> {
    program: Option<&'a mut Program>,
    builder: Builder,
    phi_ids: Vec<Operand>,

    // Ancillary state fields
    worklist: Vec<(Operand, Operand, CheckType)>, // Vec of (PhiId, BBId, CheckType)
    op_to_bb: Vec<Operand>,                       // Mapping from OpId to BBId

    // State function
    current_function: Option<usize>,
}

impl<'a> RemoveTrivialPhi<'a> {
    pub fn new() -> Self {
        Self {
            program: None,
            builder: Builder::new(),
            phi_ids: Vec::new(),
            op_to_bb: Vec::new(),
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
                    // Crucial: Treat Undefined as a concrete value, you should not ignore it.
                    if *value == phi {
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

        let mut ctx = context_or_err(
            self.program.as_deref_mut().unwrap(),
            self.current_function,
            "RemoveTrivialPhi: No current function context found",
        );
        self.op_to_bb.clear();
        self.op_to_bb
            .resize(ctx.dfg.as_ref().unwrap().storage.len(), Operand::BB(0));
        ctx.cfg
            .as_ref()
            .unwrap()
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

        self.phi_ids = self.builder.get_all_ops(&mut ctx, OpType::Phi);
        self.worklist = self
            .phi_ids
            .iter()
            .map(|phi_id| {
                let mut ctx = context_or_err(
                    self.program.as_deref_mut().unwrap(),
                    self.current_function,
                    "RemoveTrivialPhi: No current function context found",
                );
                let check_result = Self::check(&mut ctx, phi_id.clone());
                (
                    phi_id.clone(),
                    self.op_to_bb[phi_id.get_op_id()].clone(),
                    check_result,
                )
            })
            .collect();
    }

    fn remove_phi(&mut self) {
        // Check whether the phi_ids are valid
        while let Some((phi_id, bb_id, check_result)) = self.worklist.pop() {
            let uses = {
                let func_id = match self.current_function {
                    Some(id) => id,
                    None => panic!("RemoveTrivialPhi: no current function"),
                };
                let func = &mut self.program.as_mut().unwrap().funcs[func_id];
                let phi_op = &mut func.dfg[phi_id.clone()];
                // Remove OldIdx Attr
                phi_op.attrs.retain(|attr| !matches!(attr, Attr::OldIdx(_)));
                phi_op.users.clone()
            };
            let mut ctx = context_or_err(
                self.program.as_deref_mut().unwrap(),
                self.current_function,
                "RemoveTrivialPhi: No current function context found",
            );
            match check_result {
                CheckType::Empty => {
                    self.builder
                        .replace_all_uses(&mut ctx, phi_id.clone(), Operand::Undefined);
                    for user in uses {
                        // Ignore phi itself, since it will be removed later and should not pushed to worklist again.
                        if user == phi_id {
                            continue;
                        }
                        let check_result = Self::check(&mut ctx, user.clone());
                        if matches!(check_result, CheckType::Empty | CheckType::Single(_)) {
                            if let Some((id, bb)) = self
                                .phi_ids
                                .iter()
                                .find(|id| **id == user)
                                .map(|id| (id.clone(), self.op_to_bb[id.get_op_id()].clone()))
                            {
                                // We should check whether the user phi is already in the worklist to avoid duplicate entries.
                                let pos = self.worklist.iter().position(|(w_id, _, _)| *w_id == id);
                                if let Some(pos) = pos {
                                    self.worklist[pos] = (id.clone(), bb.clone(), check_result);
                                } else {
                                    self.worklist.push((id.clone(), bb.clone(), check_result));
                                }
                            }
                        }
                    }
                    self.builder.set_current_block(bb_id.clone());
                    self.builder.remove_op(&mut ctx, phi_id, Some(bb_id));
                }
                CheckType::Single(value) => {
                    self.builder
                        .replace_all_uses(&mut ctx, phi_id.clone(), value);
                    for user in uses {
                        if user == phi_id {
                            continue;
                        }
                        let check_result = Self::check(&mut ctx, user.clone());
                        if matches!(check_result, CheckType::Empty | CheckType::Single(_)) {
                            if let Some((id, bb)) = self
                                .phi_ids
                                .iter()
                                .find(|id| **id == user)
                                .map(|id| (id.clone(), self.op_to_bb[id.get_op_id()].clone()))
                            {
                                // We should check whether the user phi is already in the worklist to avoid duplicate entries.
                                let pos = self.worklist.iter().position(|(w_id, _, _)| *w_id == id);
                                if let Some(pos) = pos {
                                    self.worklist[pos] = (id.clone(), bb.clone(), check_result);
                                } else {
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
}

impl<'a> Pass<'a> for RemoveTrivialPhi<'a> {
    fn name(&self) -> &str {
        "RemoveTrivialPhi"
    }

    fn set_program(&mut self, program: &'a mut Program) {
        self.program = Some(program);
    }

    fn run(&mut self) {
        for idx in self.program.as_ref().unwrap().funcs.collect_internal() {
            self.init(idx);
            self.remove_phi();
        }
    }
}
