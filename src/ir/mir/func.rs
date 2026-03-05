use crate::base::Type;
use crate::debug::info;
use crate::ir::mir::{BasicBlock, Op, OpData, Operand, PhiIncoming, CFG, DFG};
use crate::utils::arena::*;
use std::ops::{Index, IndexMut};

pub type CG = IndexedArena<Function>;

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub is_external: bool,
    pub typ: Type,
    pub cfg: CFG,
    pub dfg: DFG,
}

impl Function {
    pub fn new(name: String, is_external: bool, typ: Type) -> Self {
        Self {
            name,
            is_external,
            typ,
            cfg: CFG::new(),
            dfg: DFG::new(),
        }
    }
}

impl Arena<Function> for IndexedArena<Function> {
    fn remove(&mut self, idx: usize) -> Function {
        if let ArenaItem::Data(data) = std::mem::replace(&mut self.storage[idx], ArenaItem::None) {
            data
        } else {
            panic!("ArenaItem is not Function Data");
        }
    }

    fn gc(&mut self) -> Vec<ArenaItem<Function>> {
        let new_arena: Vec<ArenaItem<Function>> = vec![];
        let mut old_arena = std::mem::replace(&mut self.storage, new_arena);

        // Transport
        old_arena.iter_mut().for_each(|item| {
            if matches!(item, ArenaItem::Data(_)) {
                let new_idx = self.storage.len();
                let data = item.replace(new_idx);
                self.storage.push(data);
            }
        });

        info!(
            "CG GC: {} functions collected, recycle rate: {:.2}%",
            old_arena.len() - self.storage.len(),
            (old_arena.len() - self.storage.len()) as f64 / old_arena.len() as f64 * 100.0
        );

        let remap_idx = |idx: &mut usize, old_arena: &Vec<ArenaItem<Function>>| {
            *idx = match old_arena.get(*idx) {
                Some(ArenaItem::NewIndex(new_idx)) => *new_idx,
                _ => panic!("CG gc: index {} not found", *idx),
            };
        };

        if let Some(entry) = self.entry.as_mut() {
            remap_idx(entry, &old_arena);
        }

        for idx in self.map.values_mut() {
            remap_idx(idx, &old_arena);
        }

        let remap_with_dfg = |op_idx: &mut Operand, old_arena_dfg: &Vec<ArenaItem<Op>>| {
            let old_idx = op_idx.get_op_id();
            *op_idx = match old_arena_dfg.get(old_idx) {
                Some(ArenaItem::NewIndex(new_idx)) => Operand::Value(*new_idx),
                _ => {
                    panic!("Compaction gc: op index {} in BB not found", old_idx);
                }
            };
        };

        let remap_with_cfg = |bb_idx: &mut Operand, old_arena_cfg: &Vec<ArenaItem<BasicBlock>>| {
            let old_idx = bb_idx.get_bb_id();
            *bb_idx = match old_arena_cfg.get(old_idx) {
                Some(ArenaItem::NewIndex(new_idx)) => Operand::BB(*new_idx),
                _ => {
                    panic!("Compaction gc: BB index {} in Op not found", old_idx);
                }
            };
        };

        // No need to rewrite anything inside Function for now
        self.storage.iter_mut().for_each(|func| {
            if let ArenaItem::Data(func) = func {
                if func.is_external {
                    return;
                }
                let old_arena_dfg = func.dfg.gc();
                let old_arena_cfg = func.cfg.gc();

                // rewrite op refs in BasicBlocks
                func.cfg.storage.iter_mut().for_each(|item| {
                    if let ArenaItem::Data(bb) = item {
                        for op_idx in bb.cur.iter_mut() {
                            remap_with_dfg(op_idx, &old_arena_dfg);
                        }
                    }
                });

                // rewrite BBId in dfg ops
                func.dfg.storage.iter_mut().for_each(|item| {
                    if let ArenaItem::Data(op) = item {
                        match &mut op.data {
                            OpData::Jump { target_bb } => {
                                remap_with_cfg(target_bb, &old_arena_cfg);
                            }
                            OpData::Br {
                                then_bb, else_bb, ..
                            } => {
                                remap_with_cfg(then_bb, &old_arena_cfg);
                                remap_with_cfg(else_bb, &old_arena_cfg);
                            }

                            OpData::Phi { incoming } => {
                                for phi_incoming in incoming.iter_mut() {
                                    if let PhiIncoming::Data { bb, .. } = phi_incoming {
                                        remap_with_cfg(bb, &old_arena_cfg);
                                    }
                                    // If incoming == None, do nothing
                                }
                            }

                            // Special: Call needs to rewrite the function operand.
                            OpData::Call { func, .. } => {
                                if let Operand::Func(func_id) = func {
                                    remap_idx(func_id, &old_arena);
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
                            | OpData::Declare { .. }
                            | OpData::GEP { .. }
                            | OpData::Sitofp { .. }
                            | OpData::Fptosi { .. }
                            | OpData::Zext { .. }
                            | OpData::Uitofp { .. }
                            | OpData::Ret { .. }
                            | OpData::Shl { .. }
                            | OpData::Shr { .. }
                            | OpData::Sar { .. }
                            | OpData::SNe { .. }
                            | OpData::SEq { .. }
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
                });
            }
        });

        // replace old storage
        old_arena
    }
}

impl IndexedArena<Function> {
    pub fn add(&mut self, func: Function) -> usize {
        let name = func.name.clone();
        let func_id = self.alloc(func);
        self.add_name(name, func_id);
        func_id
    }
    pub fn collect_internal(&self) -> Vec<usize> {
        self.storage
            .iter()
            .enumerate()
            .filter_map(|(idx, item)| {
                if let ArenaItem::Data(func) = item {
                    if !func.is_external {
                        Some(idx)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect()
    }
}

impl Index<Operand> for CG {
    type Output = Function;

    fn index(&self, index: Operand) -> &Self::Output {
        match index {
            Operand::Func(id) => self.get(id).unwrap(),
            _ => panic!("CG index: expected Operand::Func, got {:?}", index),
        }
    }
}

impl IndexMut<Operand> for CG {
    fn index_mut(&mut self, index: Operand) -> &mut Self::Output {
        match index {
            Operand::Func(id) => self.get_mut(id).unwrap(),
            _ => panic!("CG index_mut: expected Operand::Func, got {:?}", index),
        }
    }
}
