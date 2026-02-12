use crate::base::ir::{OpData, Operand, DFG};
use crate::utils::arena::*;

pub type CFG = IndexedArena<BasicBlock>;
pub type CG = IndexedArena<Function>;

pub struct Program {
    // global vars
    pub globals: DFG,
    // global funcs
    pub funcs: CG,
}

impl Program {
    pub fn new() -> Self {
        Self {
            globals: DFG::new(),
            funcs: CG::new(),
        }
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Function {
    pub name: String,
    pub cfg: CFG,
    pub dfg: DFG,
}

impl Function {
    pub fn new(name: String) -> Self {
        Self {
            name,
            cfg: IndexedArena::new(),
            dfg: DFG::new(),
        }
    }
}

pub struct BasicBlock {
    pub preds: Vec<Operand>,
    pub cur: Vec<Operand>,
    pub succs: Vec<Operand>,
}

impl BasicBlock {
    pub fn new() -> Self {
        Self {
            preds: vec![],
            cur: vec![],
            succs: vec![],
        }
    }
}

// impl cfg
impl Arena<BasicBlock> for IndexedArena<BasicBlock> {
    fn remove(&mut self, idx: usize) -> Result<usize, String> {
        // TODO
        unimplemented!()
    }

    fn gc(&mut self) -> Result<Vec<ArenaItem<BasicBlock>>, String> {
        let new_arena: Vec<ArenaItem<BasicBlock>> = vec![];
        let old_arena = std::mem::replace(&mut self.storage, new_arena);

        // Transport
        // CFG is a complex graph, reorder the layout seems impossible, so we just iterate the original storage directly.
        let old_arena = old_arena
            .into_iter()
            .map(|mut item| {
                if matches!(item, ArenaItem::Data(_)) {
                    let new_idx = self.storage.len();
                    let data = item.replace(new_idx);
                    self.storage.push(data);
                    ArenaItem::NewIndex(new_idx)
                } else {
                    ArenaItem::None
                }
            })
            .collect::<Vec<ArenaItem<BasicBlock>>>();

        // rewrite idx
        for item in self.storage.iter_mut() {
            // item can't be any other variant than Data here
            if let ArenaItem::Data(node) = item {
                for pred in node.preds.iter_mut() {
                    *pred = match old_arena.get(pred.get_bb_id()?).unwrap() {
                        ArenaItem::NewIndex(new_idx) => Operand::BB(*new_idx),
                        _ => {
                            return Err("CFG gc: predecessor index not found".to_string());
                        }
                    };
                }
                // rewrite data.cur needs the old arena of DFG, we'll do it in Compaction pass
                for succ in node.succs.iter_mut() {
                    *succ = match old_arena.get(succ.get_bb_id()?).unwrap() {
                        ArenaItem::NewIndex(new_idx) => Operand::BB(*new_idx),
                        _ => {
                            return Err("CFG gc: successor index not found".to_string());
                        }
                    };
                }
            }
        }

        // replace old storage
        Ok(old_arena)
    }
}

impl IndexedArena<BasicBlock> {
    pub fn add_succ(&mut self, bb_idx: Operand, succ_idx: Operand) -> Result<(), String> {
        if let Some(node) = self.get_mut(bb_idx.get_bb_id()?)? {
            node.succs.push(succ_idx);
            Ok(())
        } else {
            Err("CFG add_succ: bb index not found".to_string())
        }
    }
    pub fn add_pred(&mut self, bb_idx: Operand, pred_idx: Operand) -> Result<(), String> {
        if let Some(node) = self.get_mut(bb_idx.get_bb_id()?)? {
            node.preds.push(pred_idx);
            Ok(())
        } else {
            Err("CFG add_pred: bb index not found".to_string())
        }
    }
}

impl Arena<Function> for IndexedArena<Function> {
    fn remove(&mut self, idx: usize) -> Result<usize, String> {
        // TODO
        todo!()
    }

    fn gc(&mut self) -> Result<Vec<ArenaItem<Function>>, String> {
        let new_arena: Vec<ArenaItem<Function>> = vec![];
        let old_arena = std::mem::replace(&mut self.storage, new_arena);

        // Transport
        let old_arena = old_arena
            .into_iter()
            .map(|mut item| {
                if matches!(item, ArenaItem::Data(_)) {
                    let new_idx = self.storage.len();
                    let data = item.replace(new_idx);
                    self.storage.push(data);
                    ArenaItem::NewIndex(new_idx)
                } else {
                    ArenaItem::None
                }
            })
            .collect::<Vec<ArenaItem<Function>>>();

        // No need to rewrite anything inside Function for now
        self.storage
            .iter_mut()
            .try_for_each(|func| -> Result<(), String> {
                if let ArenaItem::Data(func) = func {
                    let old_arena_dfg = func.dfg.gc()?;
                    let old_arena_cfg = func.cfg.gc()?;
                    // TODO: We don't need to clean globals for now.

                    // rewrite op refs in BasicBlocks
                    func.cfg
                        .storage
                        .iter_mut()
                        .try_for_each(|item| -> Result<(), String> {
                            if let ArenaItem::Data(bb) = item {
                                for op_idx in bb.cur.iter_mut() {
                                    *op_idx = match old_arena_dfg.get(op_idx.get_op_id()?).unwrap()
                                    {
                                        ArenaItem::NewIndex(new_idx) => Operand::Value(*new_idx),
                                        _ => {
                                            return Err("Compaction gc: op index in BB not found"
                                                .to_string());
                                        }
                                    };
                                }
                            }
                            Ok(())
                        })?;

                    // rewrite BBId in dfg ops
                    func.dfg
                        .storage
                        .iter_mut()
                        .try_for_each(|item| -> Result<(), String> {
                            if let ArenaItem::Data(op) = item {
                                match &mut op.data {
                                    OpData::Jump { target_bb } => {
                                        *target_bb = match old_arena_cfg
                                            .get(target_bb.get_bb_id()?)
                                            .unwrap()
                                        {
                                            ArenaItem::NewIndex(new_idx) => Operand::BB(*new_idx),
                                            _ => {
                                                return Err(
                                                    "Compaction gc: BB index in Op not found"
                                                        .to_string(),
                                                );
                                            }
                                        };
                                    }
                                    OpData::Br {
                                        then_bb, else_bb, ..
                                    } => {
                                        *then_bb = match old_arena_cfg
                                            .get(then_bb.get_bb_id()?)
                                            .unwrap()
                                        {
                                            ArenaItem::NewIndex(new_idx) => Operand::BB(*new_idx),
                                            _ => {
                                                return Err(
                                                    "Compaction gc: BB index in Op not found"
                                                        .to_string(),
                                                );
                                            }
                                        };
                                        if let Some(else_bb) = else_bb {
                                            *else_bb = match old_arena_cfg
                                                .get(else_bb.get_bb_id()?)
                                                .unwrap()
                                            {
                                                ArenaItem::NewIndex(new_idx) => {
                                                    Operand::BB(*new_idx)
                                                }
                                                _ => {
                                                    return Err(
                                                        "Compaction gc: BB index in Op not found"
                                                            .to_string(),
                                                    );
                                                }
                                            };
                                        }
                                    }

                                    OpData::Phi { incoming } => {
                                        for (_val, bb_idx) in incoming.iter_mut() {
                                            *bb_idx = match old_arena_cfg
                                                .get(bb_idx.get_bb_id()?)
                                                .unwrap()
                                            {
                                                ArenaItem::NewIndex(new_idx) => {
                                                    Operand::BB(*new_idx)
                                                }
                                                _ => {
                                                    return Err(
                                                        "Compaction gc: BB index in Op not found"
                                                            .to_string(),
                                                    );
                                                }
                                            };
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
                                    | OpData::Load { .. }
                                    | OpData::Store { .. }
                                    | OpData::Alloca(_)
                                    | OpData::GlobalAlloca { .. }
                                    | OpData::GetArg { .. }
                                    | OpData::Int(_)
                                    | OpData::Float(_)
                                    | OpData::Call { .. }
                                    | OpData::Move { .. }
                                    | OpData::GEP { .. }
                                    | OpData::Sitofp { .. }
                                    | OpData::Fptosi { .. }
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
                                    | OpData::OLe { .. } => { /* no BBId to rewrite */ }
                                }
                            }
                            Ok(())
                        })?;
                }
                Ok(())
            })?;

        // replace old storage
        Ok(old_arena)
    }
}

impl IndexedArena<Function> {
    pub fn add(&mut self, func: Function) -> Result<usize, String> {
        Ok(self.alloc(func)?)
    }
}
