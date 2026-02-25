use crate::base::ir::*;
use crate::utils::arena::{Arena, ArenaItem};

use std::ops::{Deref, DerefMut};

macro_rules! acquire_cfg {
    ($ctx:ident, $msg:expr) => {
        if $ctx.cfg.is_none() {
            panic!("{}", $msg);
        } else {
            $ctx.cfg.as_mut().unwrap()
        }
    };
}

macro_rules! acquire_dfg {
    ($ctx:ident, $msg:expr) => {
        if $ctx.dfg.is_none() {
            panic!("{}", $msg);
        } else {
            $ctx.dfg.as_mut().unwrap()
        }
    };
}

#[derive(Debug, Clone)]
pub struct LoopInfo {
    pub while_entry: Option<Operand>,
    pub end_block: Option<Operand>,
}

pub struct Builder {
    pub loop_stack: Vec<LoopInfo>,
    // current basic block
    pub current_block: Option<Operand>,
    // current instruction
    pub current_inst: Option<Operand>,
}

pub struct BuilderGuard<'a> {
    pub builder: &'a mut Builder,
    loop_stack: Vec<LoopInfo>,
    // current basic block
    current_block: Option<Operand>,
    // current instruction
    current_inst: Option<Operand>,
}

impl<'a> BuilderGuard<'a> {
    pub fn new(builder: &'a mut Builder) -> Self {
        let loop_stack = builder.loop_stack.clone();
        let current_block = builder.current_block.clone();
        let current_inst = builder.current_inst.clone();
        Self {
            builder,
            loop_stack,
            current_block,
            current_inst,
        }
    }
}

// Transparent Proxy
impl Deref for BuilderGuard<'_> {
    type Target = Builder;

    fn deref(&self) -> &Self::Target {
        self.builder
    }
}

impl DerefMut for BuilderGuard<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.builder
    }
}

impl Drop for BuilderGuard<'_> {
    fn drop(&mut self) {
        self.builder.loop_stack = self.loop_stack.clone();
        self.builder.current_block = self.current_block.clone();
        self.builder.current_inst = self.current_inst.clone();
    }
}

pub struct BuilderContext<'a> {
    // current function
    pub cfg: Option<&'a mut CFG>,
    pub dfg: Option<&'a mut DFG>,
    // global vars
    pub globals: &'a mut DFG,
}

impl Builder {
    pub fn new() -> Self {
        Self {
            loop_stack: vec![],
            current_block: None,
            current_inst: None,
        }
    }

    pub fn push_loop(&mut self, loop_info: LoopInfo) {
        self.loop_stack.push(loop_info);
    }

    pub fn pop_loop(&mut self) -> Option<LoopInfo> {
        self.loop_stack.pop()
    }

    pub fn current_loop(&mut self) -> Option<&mut LoopInfo> {
        self.loop_stack.last_mut()
    }

    pub fn set_current_block(&mut self, block_id: Operand) {
        // Emm... just set current_block, no check.
        self.current_block = Some(block_id);
        // update current_inst, set to end of the block by default(Since we don't know whether the block has instructions or not)
        self.current_inst = None;
    }

    // set builder's location before inst
    // None: at the end
    // current_inst must be an instruction in the current block
    pub fn set_before_inst(&mut self, ctx: &mut BuilderContext, inst_id: Option<Operand>) {
        let cfg = acquire_cfg!(ctx, "Builder set_before_inst: ctx.cfg is None");
        if self.current_block.is_none() {
            panic!("Builder set_before_inst: current_block is None");
        };

        let current_block = self.current_block.as_ref().unwrap().get_bb_id();
        let bb = &mut cfg[current_block];
        if inst_id.is_none() {
            // set to the end of the block
            self.current_inst = None;
            return;
        }
        if bb.cur.contains(&inst_id.clone().unwrap()) {
            self.current_inst = inst_id;
        } else {
            panic!(
                "Builder set_before_inst: inst {:?} not in current_block {:?}",
                inst_id, self.current_block
            );
        }
    }

    pub fn set_after_inst(&mut self, ctx: &mut BuilderContext, inst_id: Option<Operand>) {
        let cfg = acquire_cfg!(ctx, "Builder set_after_inst: ctx.cfg is None");
        if self.current_block.is_none() {
            panic!("Builder set_after_inst: current_block is None");
        };

        let current_block = self.current_block.as_ref().unwrap().get_bb_id();
        let bb = &mut cfg[current_block];
        if inst_id.is_none() {
            // set to the end of the block
            self.current_inst = None;
            return;
        }
        if bb.cur.contains(&inst_id.clone().unwrap()) {
            // set to after the instruction, which means the next instruction is current_inst
            let pos = bb
                .cur
                .iter()
                .position(|id| id == &inst_id.clone().unwrap())
                .unwrap_or_else(|| {
                    panic!(
                        "Builder set_after_inst: inst {:?} not found in current_block {:?}",
                        inst_id, self.current_block
                    )
                });
            if pos + 1 < bb.cur.len() {
                self.current_inst = Some(bb.cur[pos + 1].clone());
            } else {
                // set to the end of the block
                self.current_inst = None;
            }
        } else {
            panic!(
                "Builder set_after_inst: inst {:?} not in current_block {:?}",
                inst_id, self.current_block
            );
        }
    }

    // constructing data flow
    pub fn add_uses(&mut self, ctx: &mut BuilderContext, op: Operand) {
        let dfg = acquire_dfg!(ctx, "Builder add_users: ctx.dfg is None");
        let globals = &mut ctx.globals;
        let data = dfg[op.get_op_id()].data.clone();

        match data {
            OpData::Load { addr } => {
                if matches!(addr, Operand::Global(_)) {
                    // For global variables, we don't maintain uses in the DFG, so just return.
                    globals.add_use(addr, op.clone());
                } else if matches!(addr, Operand::Value(_)) {
                    dfg.add_use(addr, op);
                } else {
                    panic!("Builder add_uses: Load address operand is not Value or Global");
                }
            }
            OpData::Store { addr, value } => {
                if matches!(addr, Operand::Global(_)) {
                    // For global variables, we don't maintain uses in the DFG, so just return.
                    globals.add_use(addr, op.clone());
                } else if matches!(addr, Operand::Value(_)) {
                    dfg.add_use(addr, op.clone());
                } else {
                    panic!("Builder add_uses: Store address operand is not Value or Global");
                }
                dfg.add_use(value, op);
            }
            OpData::Br { cond, .. } => {
                dfg.add_use(cond, op);
            }
            OpData::Call { args, .. } => {
                for arg in args {
                    dfg.add_use(arg, op.clone());
                }
            }
            OpData::Ret { value } => {
                if let Some(val) = value {
                    dfg.add_use(val, op);
                }
            }
            OpData::Phi { incoming } => {
                for phi_incoming in incoming {
                    if let PhiIncoming::Data { value, .. } = phi_incoming {
                        dfg.add_use(value, op.clone());
                    }
                }
            }

            OpData::AddI { lhs, rhs }
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
            | OpData::AddF { lhs, rhs }
            | OpData::SubF { lhs, rhs }
            | OpData::MulF { lhs, rhs }
            | OpData::DivF { lhs, rhs }
            | OpData::ONe { lhs, rhs }
            | OpData::OEq { lhs, rhs }
            | OpData::OGt { lhs, rhs }
            | OpData::OLt { lhs, rhs }
            | OpData::OGe { lhs, rhs }
            | OpData::OLe { lhs, rhs } => {
                dfg.add_use(lhs, op.clone());
                dfg.add_use(rhs, op);
            }

            OpData::Sitofp { value } | OpData::Fptosi { value } | OpData::Uitofp { value } | OpData::Zext { value } => {
                dfg.add_use(value, op);
            }

            OpData::GEP { base, indices } => {
                if matches!(base, Operand::Global(_)) {
                    globals.add_use(base, op.clone());
                } else if matches!(base, Operand::Value(_)) {
                    dfg.add_use(base, op.clone());
                } else {
                    panic!("Builder add_uses: GEP base operand is not Value or Global");
                }
                for index in indices {
                    dfg.add_use(index, op.clone());
                }
            }

            OpData::Move { value, .. } => {
                dfg.add_use(value, op);
            }

            // GlobalAlloca: Do not maintain uses for global alloca
            OpData::GlobalAlloca(_)
            // ?
            | OpData::Alloca(_)
            | OpData::Jump {..}
            | OpData::Declare {..} => { /* do nothing */ }
        }
    }

    // Remove CURRENT Op from Another one's USERS.
    pub fn remove_uses(&mut self, ctx: &mut BuilderContext, op: Operand) {
        let dfg = acquire_dfg!(ctx, "Builder remove_users: ctx.dfg is None");
        let globals = &mut ctx.globals;
        let data = dfg[op.get_op_id()].data.clone();

        match data {
            OpData::Load { addr } => {
                if matches!(addr, Operand::Global(_)) {
                    globals.remove_use(addr, op);
                } else if matches!(addr, Operand::Value(_)) {
                    dfg.remove_use(addr, op);
                } else {
                    panic!("Builder remove_uses: Load address operand is not Value or Global");
                }
            }
            OpData::Store { addr, value } => {
                if matches!(addr, Operand::Global(_)) {
                    globals.remove_use(addr, op.clone());
                } else if matches!(addr, Operand::Value(_)) {
                    dfg.remove_use(addr, op.clone());
                } else {
                    panic!("Builder remove_uses: Store address operand is not Value or Global");
                }
                dfg.remove_use(value, op);
            }
            OpData::Br { cond, .. } => {
                dfg.remove_use(cond, op);
            }
            OpData::Call { args, .. } => {
                for arg in args {
                    dfg.remove_use(arg, op.clone());
                }
            }
            OpData::Ret { value } => {
                if let Some(val) = value {
                    dfg.remove_use(val, op);
                }
            }
            OpData::Phi { incoming } => {
                let mut removed = vec![];
                for phi_incoming in incoming {
                    if let PhiIncoming::Data { value, .. } = phi_incoming {
                        if !removed.contains(&value) {
                            removed.push(value.clone());
                        } else {
                            continue;
                        }
                        // Critical: We only delete one value once, otherwise a double delete will cause a panic.
                        dfg.remove_use(value, op.clone());
                    }
                }
            }

            OpData::AddI { lhs, rhs }
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
            | OpData::AddF { lhs, rhs }
            | OpData::SubF { lhs, rhs }
            | OpData::MulF { lhs, rhs }
            | OpData::DivF { lhs, rhs }
            | OpData::ONe { lhs, rhs }
            | OpData::OEq { lhs, rhs }
            | OpData::OGt { lhs, rhs }
            | OpData::OLt { lhs, rhs }
            | OpData::OGe { lhs, rhs }
            | OpData::OLe { lhs, rhs } => {
                dfg.remove_use(lhs, op.clone());
                dfg.remove_use(rhs, op);
            }
            OpData::Sitofp { value } | OpData::Fptosi { value } | OpData::Uitofp { value } | OpData::Zext { value } => {
                dfg.remove_use(value, op);
            }

            OpData::GEP { base, indices } => {
                if matches!(base, Operand::Global(_)) {
                    globals.remove_use(base, op.clone());
                } else if matches!(base, Operand::Value(_)) {
                    dfg.remove_use(base, op.clone());
                } else {
                    panic!("Builder remove_uses: GEP base operand is not Value or Global");
                }
                for index in indices {
                    dfg.remove_use(index, op.clone());
                }
            }
            OpData::Move { value, .. } => {
                dfg.remove_use(value, op);
            }
            OpData::GlobalAlloca(_)
            | OpData::Alloca(_)
            | OpData::Jump { .. }
            | OpData::Declare { .. } => { /* do nothing */ }
        }
    }

    pub fn replace_all_uses(&mut self, ctx: &mut BuilderContext, old: Operand, new: Operand) {
        let dfg = acquire_dfg!(ctx, "Builder replace_all_uses: ctx.dfg is None");
        let uses = &dfg[old.get_op_id()].users.clone();
        for use_op in uses {
            dfg.replace_use(use_op.clone(), old.clone(), new.clone());
        }
    }

    // constructing control flow
    pub fn add_control_flow(&mut self, ctx: &mut BuilderContext, op: Operand) {
        let cfg = acquire_cfg!(ctx, "Builder add_control_flow: ctx.cfg is None");
        let dfg = acquire_dfg!(ctx, "Builder add_control_flow: ctx.dfg is None");

        let data = dfg[op.get_op_id()].data.clone();

        let current_bb = if self.current_block.is_none() {
            panic!("Builder add_control_flow: current_block is None");
        } else {
            self.current_block.as_ref().unwrap().clone()
        };

        match data {
            OpData::Br {
                then_bb, else_bb, ..
            } => {
                cfg.add_pred(then_bb.clone(), current_bb.clone());
                cfg.add_succ(current_bb.clone(), then_bb);
                cfg.add_pred(else_bb.clone(), current_bb.clone());
                cfg.add_succ(current_bb, else_bb);
            }
            OpData::Jump { target_bb } => {
                cfg.add_pred(target_bb.clone(), current_bb.clone());
                cfg.add_succ(current_bb, target_bb);
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
            | OpData::Load { .. }
            | OpData::Store { .. }
            | OpData::Alloca(_)
            | OpData::Phi { .. }
            | OpData::GlobalAlloca { .. }
            | OpData::Call { .. }
            | OpData::Move { .. }
            | OpData::GEP { .. }
            | OpData::Sitofp { .. }
            | OpData::Fptosi { .. }
            | OpData::Uitofp { .. }
            | OpData::Zext { .. }
            | OpData::Ret { .. }
            | OpData::Shl { .. }
            | OpData::Shr { .. }
            | OpData::Sar { .. }
            | OpData::SNe { .. }
            | OpData::SEq { .. }
            | OpData::And { .. }
            | OpData::Or { .. }
            | OpData::Xor { .. }
            | OpData::SGt { .. }
            | OpData::SLt { .. }
            | OpData::SGe { .. }
            | OpData::SLe { .. }
            | OpData::ONe { .. }
            | OpData::OEq { .. }
            | OpData::OGt { .. }
            | OpData::OLt { .. }
            | OpData::OGe { .. }
            | OpData::OLe { .. }
            | OpData::Declare { .. } => { /* do nothing */ }
        }
    }

    pub fn remove_control_flow(&mut self, ctx: &mut BuilderContext, op: Operand) {
        let cfg = acquire_cfg!(ctx, "Builder remove_control_flow: ctx.cfg is None");
        let dfg = acquire_dfg!(ctx, "Builder remove_control_flow: ctx.dfg is None");
        let data = dfg[op.get_op_id()].data.clone();

        let current_bb = if self.current_block.is_none() {
            panic!("Builder remove_control_flow: current_block is None");
        } else {
            self.current_block.as_ref().unwrap().clone()
        };

        match data {
            OpData::Br {
                then_bb, else_bb, ..
            } => {
                cfg.remove_pred(then_bb.clone(), current_bb.clone());
                cfg.remove_succ(current_bb.clone(), then_bb);
                cfg.remove_pred(else_bb.clone(), current_bb.clone());
                cfg.remove_succ(current_bb, else_bb);
            }
            OpData::Jump { target_bb } => {
                cfg.remove_pred(target_bb.clone(), current_bb.clone());
                cfg.remove_succ(current_bb, target_bb);
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
            | OpData::Load { .. }
            | OpData::Store { .. }
            | OpData::Alloca(_)
            | OpData::Phi { .. }
            | OpData::GlobalAlloca { .. }
            | OpData::Call { .. }
            | OpData::Move { .. }
            | OpData::GEP { .. }
            | OpData::Sitofp { .. }
            | OpData::Fptosi { .. }
            | OpData::Uitofp { .. }
            | OpData::Zext { .. }
            | OpData::Ret { .. }
            | OpData::Shl { .. }
            | OpData::Shr { .. }
            | OpData::Sar { .. }
            | OpData::SNe { .. }
            | OpData::SEq { .. }
            | OpData::And { .. }
            | OpData::Or { .. }
            | OpData::Xor { .. }
            | OpData::SGt { .. }
            | OpData::SLt { .. }
            | OpData::SGe { .. }
            | OpData::SLe { .. }
            | OpData::ONe { .. }
            | OpData::OEq { .. }
            | OpData::OGt { .. }
            | OpData::OLt { .. }
            | OpData::OGe { .. }
            | OpData::OLe { .. }
            | OpData::Declare { .. } => { /* do nothing*/ }
        }
    }

    // create an instruction after current instruction
    pub fn create(&mut self, ctx: &mut BuilderContext, op: Op) -> Operand {
        let op_id = match op.data {
            OpData::GlobalAlloca(_) => {
                let globals = &mut ctx.globals;
                let op_id = globals.alloc(op);
                // Distinguish global alloca from normal local variables. They don't share the same namespace.
                Operand::Global(op_id)
            }
            OpData::Declare { .. } => {
                let globals = &mut ctx.globals;
                let op_id = globals.alloc(op);
                Operand::Global(op_id)
            }

            OpData::GEP { .. }
            | OpData::Move { .. }
            | OpData::AddI { .. }
            | OpData::SubI { .. }
            | OpData::MulI { .. }
            | OpData::DivI { .. }
            | OpData::ModI { .. }
            | OpData::And { .. }
            | OpData::Or { .. }
            | OpData::Xor { .. }
            | OpData::SNe { .. }
            | OpData::SEq { .. }
            | OpData::SGt { .. }
            | OpData::SLt { .. }
            | OpData::SGe { .. }
            | OpData::SLe { .. }
            | OpData::Shl { .. }
            | OpData::Shr { .. }
            | OpData::Sar { .. }
            | OpData::AddF { .. }
            | OpData::SubF { .. }
            | OpData::MulF { .. }
            | OpData::DivF { .. }
            | OpData::ONe { .. }
            | OpData::OEq { .. }
            | OpData::OGt { .. }
            | OpData::OLt { .. }
            | OpData::OGe { .. }
            | OpData::OLe { .. }
            | OpData::Sitofp { .. }
            | OpData::Fptosi { .. }
            | OpData::Uitofp { .. }
            | OpData::Zext { .. }
            | OpData::Store { .. }
            | OpData::Load { .. }
            | OpData::Phi { .. }
            | OpData::Alloca(_)
            | OpData::Call { .. }
            | OpData::Br { .. }
            | OpData::Jump { .. }
            | OpData::Ret { .. } => {
                let dfg = acquire_dfg!(ctx, "Builder create: ctx.dfg is None");
                let cfg = acquire_cfg!(ctx, "Builder create: ctx.cfg is None");

                // append_at will update the prev and next pointers accordingly
                let op_id = dfg.alloc(op);
                let current_block = if let Some(block) = &self.current_block {
                    block.get_bb_id()
                } else {
                    panic!("Builder create: current_block is None");
                };
                let bb = &mut cfg[current_block];

                let op_id = if let Some(current_inst) = &self.current_inst {
                    // insert before current_inst
                    let pos = bb
                        .cur
                        .iter()
                        .position(|id| {
                            let id = id.get_op_id();
                            let inst_id = current_inst.get_op_id();
                            id == inst_id
                        })
                        .unwrap_or_else(|| {
                            panic!(
                                "Builder create: current_inst {:?} not found in current_block {:?}",
                                current_inst, self.current_block
                            )
                        });
                    let op_id = Operand::Value(op_id);
                    bb.cur.insert(pos, op_id.clone());
                    op_id
                } else {
                    // insert at the end
                    let op_id = Operand::Value(op_id);
                    bb.cur.push(op_id.clone());
                    op_id
                };
                // add uses
                self.add_uses(ctx, op_id.clone());
                // add control flow info if needed
                self.add_control_flow(ctx, op_id.clone());
                // We don't update current_inst, so that the next created instruction is still before the same instruction
                op_id
            }
        };
        op_id
    }

    pub fn create_at_head(&mut self, ctx: &mut BuilderContext, op: Op) -> Operand {
        let bb_id = match &self.current_block {
            Some(block) => block.get_bb_id(),
            None => panic!("Builder create_at_head: current_block is None"),
        };
        // if no instruction in the block, insert at the end, otherwise insert before the first instruction
        let inst_id = {
            let cfg = acquire_cfg!(ctx, "Builder create_at_head: ctx.cfg is None");
            let bb = &cfg[bb_id];
            if bb.cur.is_empty() {
                None
            } else {
                Some(bb.cur[0].clone())
            }
        };

        self.set_before_inst(ctx, inst_id);
        self.create(ctx, op)
    }

    pub fn create_new_block(&mut self, ctx: &mut BuilderContext) -> Operand {
        let cfg = acquire_cfg!(ctx, "Builder create_new_block: ctx.cfg is None");
        let bb_id = cfg.alloc(BasicBlock::new());
        // we separate block creation and setting current block
        Operand::BB(bb_id)
    }

    pub fn get_all_ops(&self, ctx: &mut BuilderContext, op_typ: OpType) -> Vec<Operand> {
        let dfg = acquire_dfg!(ctx, "Builder get_all_ops: ctx.dfg is None");
        dfg.storage
            .iter()
            .enumerate()
            .filter_map(|(idx, item)| {
                if let ArenaItem::Data(node) = item {
                    if node.is(op_typ) {
                        Some(Operand::Value(idx))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect::<Vec<Operand>>()
    }

    pub fn get_all_ops_in_block(
        &self,
        ctx: &mut BuilderContext,
        block: Operand,
        op_typ: OpType,
    ) -> Vec<Operand> {
        let cfg = acquire_cfg!(ctx, "Builder get_all_ops_in_block: ctx.cfg is None");
        let dfg = acquire_dfg!(ctx, "Builder get_all_ops_in_block: ctx.dfg is None");

        let bb_id = block.get_bb_id();
        let bb = &cfg[bb_id];

        let mut ops = Vec::new();
        for inst in &bb.cur {
            let data = &dfg[inst.get_op_id()];
            if data.is(op_typ) {
                ops.push(inst.clone());
            }
        }
        ops
    }

    pub fn remove_op(&mut self, ctx: &mut BuilderContext, op: Operand, bb: Option<Operand>) -> Op {
        // remove uses first, otherwise we may have use-after-free in the DFG.
        self.remove_uses(ctx, op.clone());
        // Remove control flow info if needed
        self.remove_control_flow(ctx, op.clone());

        let dfg = acquire_dfg!(ctx, "Builder remove_op: ctx.dfg is None");
        let cfg = acquire_cfg!(ctx, "Builder remove_op: ctx.cfg is None");

        let removed_op = match dfg[op.get_op_id()].data.clone() {
            OpData::GlobalAlloca(_) => {
                // For global alloca, we just remove it from the global variables, and do not maintain uses for it in the DFG, so we can just return here.
                let globals = &mut ctx.globals;
                globals.remove(op.get_op_id())
            }
            _ => {
                let op_id = op.get_op_id();
                let bb_id = match bb {
                    Some(bb) => bb.get_bb_id(),
                    None => panic!(
                        "Builder remove_op: bb is None when removing instruction {:?}",
                        op
                    ),
                };
                let bb = &mut cfg[bb_id];

                // remove from bb
                if let Some(pos) = bb.cur.iter().position(|id| id.get_op_id() == op_id) {
                    bb.cur.remove(pos);
                } else {
                    panic!(
                        "Builder remove_op: instruction {:?} not found in current_block {:?}",
                        op, bb_id
                    );
                }

                // remove from dfg
                dfg.remove(op_id)
            }
        };
        // Check the users of the remove op. For now, if users exist, we just panic.
        if !removed_op.users.is_empty() {
            panic!(
                "Builder remove_op: instruction {:?} still has users after removal. users: {:?}",
                removed_op,
                removed_op
                    .users
                    .iter()
                    .map(|user| {
                        let op = &dfg[user.get_op_id()];
                        format!("{:?}: {:?}", user, op)
                    })
                    .collect::<Vec<String>>()
                    .join(", ")
            );
        }
        removed_op
    }

    // Move the instruction to the front of specific position(operantion) in another basic block.
    pub fn move_op_to_bb_at(
        &mut self,
        ctx: &mut BuilderContext,
        op: Operand,
        old_bb: Operand,
        new_bb: Operand,
        pos: Option<Operand>,
    ) {
        let cfg = acquire_cfg!(ctx, "Builder move_op_to_bb_at: ctx.cfg is None");

        let op_id = op.get_op_id();
        let old_bb_id = old_bb.get_bb_id();

        // remove from old bb
        let old_bb = &mut cfg[old_bb_id];
        if let Some(pos) = old_bb.cur.iter().position(|id| id.get_op_id() == op_id) {
            old_bb.cur.remove(pos);
        } else {
            panic!(
                "Builder move_op_to_bb_at: instruction {:?} not found in old_bb {:?}",
                op, old_bb
            );
        }

        let new_bb_id = new_bb.get_bb_id();
        // insert into new bb at pos
        let new_bb = &mut cfg[new_bb_id];
        if let Some(pos) = pos {
            let pos_id = pos.get_op_id();
            if let Some(pos) = new_bb.cur.iter().position(|id| id.get_op_id() == pos_id) {
                new_bb.cur.insert(pos, op.clone());
            } else {
                panic!(
                    "Builder move_op_to_bb_at: instruction {:?} not found in new_bb {:?}",
                    pos, new_bb
                );
            }
        } else {
            new_bb.cur.push(op.clone());
        }
    }

    pub fn add_phi_incoming(
        &mut self,
        ctx: &mut BuilderContext,
        phi: Operand,
        idx: usize,
        value: Operand,
        bb: Operand,
    ) {
        let dfg = acquire_dfg!(ctx, "Builder insert_phi_incoming: ctx.dfg is None");

        let phi_id = phi.get_op_id();

        // Check if the phi already has an incoming from the bb. If yes, we just update the value.
        if let OpData::Phi { incoming } = &mut dfg[phi_id].data {
            incoming[idx] = PhiIncoming::Data {
                value: value.clone(),
                bb,
            };
            // add uses. do not use self.add_users since it will add use for the phi node itself, which is not what we want.
            dfg.add_use(value, phi.clone());
        } else {
            panic!("Builder insert_phi_incoming: not a phi node");
        }
    }
}
