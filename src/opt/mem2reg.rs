/// SSA construction & Mem2Reg based on Cytron et al. 1991's algorithm.
/// Reference: https://dl.acm.org/doi/pdf/10.1145/75277.75280
use crate::analysis::dom::{BuildDomFrontier, BuildDomTree, DomFrontier, DomTree};
use crate::base::{context_or_err, Builder, BuilderGuard, Pass, Type};
use crate::debug::info;
use crate::ir::mir::{Attr, Op, OpData, OpType, Operand, PhiIncoming, Program};

use std::collections::HashMap;

struct InsertPhi<'a> {
    program: &'a mut Program,
    builder: Builder,
    // Former computed frontiers
    frontiers: Vec<DomFrontier>,

    // Ancillary state fields
    // VarId -> Vec of BBId
    defsites: Vec<Vec<usize>>,
    // The original defs in BBId, BBId -> Vec of OpId
    origins: Vec<Vec<usize>>,
    // The BBId that contains a phi for OpId, VarId -> Vec of BBId
    phis: Vec<Vec<usize>>,

    // Temporary map from OpId to VarId to avoid sparse indexing of the above structures
    // FuncId -> OpId -> VarId
    op_to_var: HashMap<usize, usize>,
    var_to_op: HashMap<usize, usize>,
    var_counter: usize,

    // State field
    current_function: Option<usize>,

    // Phis' id
    // Vec<(OpId, BBId)>
    phi_ids: Vec<Vec<(Operand, Operand)>>,
}

impl<'a> InsertPhi<'a> {
    pub fn new(program: &'a mut Program, frontiers: Vec<DomFrontier>) -> Self {
        Self {
            program,
            builder: Builder::new(),
            frontiers,
            defsites: vec![],
            origins: vec![],
            phis: vec![],
            op_to_var: HashMap::new(),
            var_to_op: HashMap::new(),
            var_counter: 0,
            current_function: None,
            phi_ids: vec![],
        }
    }

    pub fn init(&mut self, idx: usize) {
        self.op_to_var.clear();
        self.var_to_op.clear();
        self.var_counter = 0;

        let (cfg_len, allocas) = {
            self.current_function = Some(idx);
            let func = &self.program.funcs[idx];
            let cfg_len = func.cfg.storage.len();
            let mut ctx = context_or_err(
                self.program,
                self.current_function,
                "InsertPhi: No current function context found",
            );
            (cfg_len, self.builder.get_all_ops(&mut ctx, OpType::Alloca))
        };

        // Initialize the map between OpId and VarId
        for alloca in allocas.into_iter() {
            let op_id = match alloca {
                Operand::Value(id) => id,
                _ => panic!("InsertPhi: allocas contains non-op"),
            };
            let var_id = self.var_counter;
            self.var_counter += 1;

            self.op_to_var.insert(op_id, var_id);
            self.var_to_op.insert(var_id, op_id);
        }

        self.defsites = vec![vec![]; self.var_counter];
        self.origins = vec![vec![]; cfg_len];
        self.phis = vec![vec![]; self.var_counter];

        // Compute defsites, origins and phis
        let func_id = self.current_function.unwrap();
        let bb_ids = self.program.funcs[func_id].cfg.collect();
        for bb_id in bb_ids {
            let func = &self.program.funcs[func_id];
            let block = &func.cfg[bb_id];
            for op_id_operand in &block.cur {
                let op = &func.dfg[op_id_operand.clone()];
                if op.is(OpType::Store) {
                    let addr = match &op.data {
                        OpData::Store { addr, .. } => addr,
                        _ => panic!("InsertPhi: expected store op"),
                    };

                    if let Operand::Value(addr_id) = addr {
                        let addr_op = &func.dfg[addr.clone()];
                        if !addr_op
                            .attrs
                            .iter()
                            .any(|attr| matches!(attr, Attr::Promotion))
                        {
                            // If the store address doesn't have OldIdx attribute, it might not be a relevant store for mem2reg (e.g., global or array), so we skip it.
                            continue;
                        }

                        if let Some(&var_id) = self.op_to_var.get(addr_id) {
                            self.defsites[var_id].push(bb_id);
                            self.origins[bb_id].push(var_id);
                        }
                    }
                    // If it's not in op_to_var, it might not be a relevant store for mem2reg (e.g., global or array), so we skip it.
                }
            }
        }
    }

    pub fn insert(&mut self) -> Vec<(Operand, Operand)> {
        let mut phi_ids = vec![];

        let defsites_len = self.defsites.len();
        let func_id = self.current_function.unwrap();
        for idx in 0..defsites_len {
            while let Some(bb_id) = self.defsites[idx].pop() {
                let frontiers = self.frontiers[func_id][bb_id].clone();
                for frontier in frontiers {
                    // If the phi already exists, we don't need to insert it again, but we still need to update the origins.
                    if !self.phis[idx].contains(&frontier) {
                        // Get number of preds of the frontier block
                        let preds_num = {
                            let func = &self.program.funcs[func_id];
                            let block = &func.cfg[frontier];
                            block.preds.len()
                        };
                        // Insert phi
                        // Use guard to save the old context
                        let phi_op_id = {
                            let mut guard = BuilderGuard::new(&mut self.builder);

                            guard.set_current_block(Operand::BB(frontier));

                            // Get type of the variable from one of its original defs.
                            let var_type = {
                                let func = &self.program.funcs[func_id];
                                let origin_op_id = match self.var_to_op.get(&idx) {
                                    Some(id) => *id,
                                    None => {
                                        panic!("InsertPhi: variable has no original definition")
                                    }
                                };

                                // This is an alloca
                                let origin_op = &func.dfg[origin_op_id];
                                match &origin_op.typ {
                                    Type::Pointer { base } => *base.clone(),
                                    _ => {
                                        panic!("InsertPhi: original definition is not a pointer")
                                    }
                                }
                            };

                            let mut ctx = context_or_err(
                                self.program,
                                self.current_function,
                                "InsertPhi: No current function context found",
                            );
                            guard.create_at_head(
                                &mut ctx,
                                Op::new(
                                    // We don't know the inst's result type yet
                                    var_type,
                                    vec![Attr::OldIdx(Operand::Value(self.var_to_op[&idx]))],
                                    OpData::Phi {
                                        // Hold the place with dummy incoming. We will update it later.
                                        incoming: vec![PhiIncoming::None; preds_num],
                                    },
                                ),
                            )
                        };

                        // Record the phi's OpId.
                        phi_ids.push((phi_op_id, Operand::BB(frontier)));
                        self.phis[idx].push(frontier);
                        if !self.origins[frontier].contains(&idx) {
                            // If it is a new definition in the frontier block, we add the block to the var's worklist.
                            self.defsites[idx].push(frontier);
                        }
                    }
                }
            }
        }
        phi_ids
    }

    pub fn run(&mut self) -> Vec<Vec<(Operand, Operand)>> {
        self.phi_ids = vec![vec![]; self.program.funcs.storage.len()];
        self.program
            .funcs
            .collect_internal()
            .into_iter()
            .for_each(|idx| {
                self.init(idx);
                let phi_ids = self.insert();
                self.phi_ids[idx] = phi_ids;
            });
        std::mem::take(&mut self.phi_ids)
    }
}

struct Renaming<'a> {
    program: Option<&'a mut Program>,
    builder: Builder,
    dom_trees: Vec<DomTree>,
    // Record the previous "frame pointer" of the version stack
    records: Vec<Vec<usize>>,
    // version stack
    versions: Vec<Vec<Operand>>,

    // State field
    current_function: Option<usize>,

    // Temporary map from VarId to OpId to avoid sparse indexing of the above structures
    op_to_var: HashMap<usize, usize>,
    var_to_op: HashMap<usize, usize>,
    var_counter: usize,

    // The old load/store that need to be removed
    // Vec<(OpId, BBId)>
    removed: Vec<(Operand, Operand)>,
}

impl<'a> Renaming<'a> {
    pub fn new(program: &'a mut Program, dom_trees: Vec<DomTree>) -> Self {
        Self {
            program: Some(program),
            builder: Builder::new(),
            dom_trees,
            records: vec![],
            versions: vec![],
            op_to_var: HashMap::new(),
            var_to_op: HashMap::new(),
            var_counter: 0,
            current_function: None,
            removed: vec![],
        }
    }

    fn init(&mut self) {
        self.op_to_var.clear();
        self.var_to_op.clear();
        self.var_counter = 0;

        let (entry, bbs) = {
            let func = &self.program.as_ref().unwrap().funcs[self.current_function.unwrap()];
            let entry = match func.cfg.entry {
                Some(id) => id,
                None => panic!("Renaming: function has no entry block"),
            };
            let bbs = func.cfg.collect();
            (entry, bbs)
        };

        self.builder.set_current_block(Operand::BB(entry));
        let func_id = self.current_function.unwrap();
        // For each block, we check if it contains an alloca. If it does, we move the alloca to the entry block.
        for bb_id in bbs {
            let allocas = {
                let mut ctx = context_or_err(
                    self.program.as_deref_mut().unwrap(),
                    self.current_function,
                    "Renaming: No current function context found",
                );
                self.builder
                    .get_all_ops_in_block(&mut ctx, Operand::BB(bb_id), OpType::Alloca)
            };

            let mut ctx = context_or_err(
                self.program.as_deref_mut().unwrap(),
                self.current_function,
                "Renaming: No current function context found",
            );
            // Raise all the allocas to the entry block.
            for alloca in &allocas {
                // raise alloca to the entry block if it's not already in the entry block
                if bb_id != entry {
                    self.builder.move_op_to_bb_at(
                        &mut ctx,
                        alloca.clone(),
                        Operand::BB(bb_id),
                        Operand::BB(entry),
                        // Entry block has at least one jump.
                        Some(Operand::Value(0)),
                    );
                }
            }

            // Filter allocas that are not promoted (e.g., those without the Promotion attribute). We won't promote them, so we can just ignore them in renaming.
            let promoted_allocas: Vec<Operand> = allocas
                .into_iter()
                .filter(|alloca| {
                    let func = &self.program.as_ref().unwrap().funcs[func_id];
                    let alloca_op = &func.dfg[alloca.clone()];
                    alloca_op
                        .attrs
                        .iter()
                        .any(|attr| matches!(attr, Attr::Promotion))
                })
                .collect();

            // Initialize the map between OpId and VarId
            for alloca in promoted_allocas {
                let op_id = match alloca {
                    Operand::Value(id) => id,
                    _ => panic!("Renaming: allocas contains non-op"),
                };

                let var_id = self.var_counter;
                self.var_counter += 1;

                self.op_to_var.insert(op_id, var_id);
                self.var_to_op.insert(var_id, op_id);
            }
        }

        self.records = vec![vec![]; self.var_counter];
        // In some situations (e.g., when the alloca is created in a loop), the alloca might have been moved to the entry block in a previous iteration.
        // In SSA form, we can treat it as undef, so we can just simply give all vars a Operand::Undefined.
        // This is a common practice in SSA construction to handle uninitialized variables.
        self.versions = vec![vec![Operand::Undefined]; self.var_counter];
    }

    fn rename(&mut self, bb_id: usize) {
        // Record current "frame pointer"
        for var in 0..self.versions.len() {
            self.records[var].push(self.versions[var].len());
        }

        // Gather information first to avoid holding borrow of self.program.funcs
        let (insts, succs) = {
            let func = &self.program.as_ref().unwrap().funcs[self.current_function.unwrap()];
            let bb = &func.cfg[bb_id];
            let insts = bb.cur.clone();
            let succs = bb.succs.clone();
            (insts, succs)
        };

        // 1. Process instructions in current block
        for inst in insts {
            // We need to access op data.
            // We can't hold `op` borrow across replace_all_uses (which takes &mut ctx).
            // So we clone the necessary data or just check type first.
            let (op_data, op_attrs) = {
                let func = &self.program.as_ref().unwrap().funcs[self.current_function.unwrap()];
                let op = &func.dfg[inst.clone()];
                (op.data.clone(), op.attrs.clone())
            };

            match op_data {
                OpData::Store { addr, value } => {
                    match addr {
                        // Local variables, including parameter and local vars defined.
                        Operand::Value(_) | Operand::Param { .. } => {}
                        // We won't promote global variables.
                        Operand::Global(_) => continue,
                        _ => panic!("Renaming: store address is not a value or global"),
                    };

                    if let Some(&var_id) = self.op_to_var.get(&addr.get_op_id()) {
                        // Push the OpId which produces the new value.
                        self.versions[var_id].push(value);
                        self.removed.push((inst, Operand::BB(bb_id)));
                    }
                }
                OpData::Load { addr } => {
                    match addr {
                        Operand::Value(_) => {}
                        // We won't promote global variables.
                        Operand::Global(_) => continue,
                        _ => panic!("Renaming: store address is not a value or global"),
                    };

                    if let Some(&var_id) = self.op_to_var.get(&addr.get_op_id()) {
                        if let Some(version) = self.versions[var_id].last() {
                            // Replace the load with the current version
                            let new_val = version.clone();
                            let mut ctx = context_or_err(
                                self.program.as_deref_mut().unwrap(),
                                self.current_function,
                                "Renaming: No current function context found",
                            );
                            self.builder
                                .replace_all_uses(&mut ctx, inst.clone(), new_val);
                            self.removed.push((inst, Operand::BB(bb_id)));
                        } else {
                            panic!("Renaming: load from variable {} before any store", var_id);
                        }
                    }
                }
                OpData::Phi { .. } => {
                    let var_op = op_attrs.iter().find_map(|attr| {
                        if let Attr::OldIdx(Operand::Value(id)) = attr {
                            Some(*id)
                        } else {
                            None
                        }
                    });
                    if let Some(var_op_id) = var_op {
                        if let Some(&var_id) = self.op_to_var.get(&var_op_id) {
                            self.versions[var_id].push(inst.clone());
                        }
                    }
                }
                _ => { /*do nothing*/ }
            }
        }

        // 2. Process successors
        for succ in succs {
            // Calculate k (predecessor index)
            let k = {
                let func = &self.program.as_ref().unwrap().funcs[self.current_function.unwrap()];
                let succ_block = &func.cfg[succ.clone()];
                succ_block
                    .preds
                    .iter()
                    .position(|pred| match pred {
                        Operand::BB(id) => *id == bb_id,
                        _ => false,
                    })
                    .unwrap_or_else(|| {
                        panic!("Renaming: predecessor not found in successor's preds")
                    })
            };

            // Get all phis in successor
            let phis = {
                let mut ctx = context_or_err(
                    self.program.as_deref_mut().unwrap(),
                    self.current_function,
                    "Renaming: No current function context found",
                );
                self.builder
                    .get_all_ops_in_block(&mut ctx, succ.clone(), OpType::Phi)
            };

            for phi in phis {
                // Check if this phi is one we track (has a var_id)
                // Update phi incoming
                let op_id = {
                    let func =
                        &self.program.as_ref().unwrap().funcs[self.current_function.unwrap()];
                    let phi_op = &func.dfg[phi.clone()];
                    let op_id = phi_op
                        .attrs
                        .iter()
                        .find_map(|attr| {
                            if let Attr::OldIdx(Operand::Value(id)) = attr {
                                Some(*id)
                            } else {
                                None
                            }
                        })
                        .unwrap_or_else(|| panic!("Renaming: phi op missing OldIdx attribute"));
                    op_id
                };

                if let Some(&var_id) = self.op_to_var.get(&op_id) {
                    if let Some(version) = self.versions[var_id].last().cloned() {
                        // Update phi incoming
                        self.builder.add_phi_incoming(
                            &mut context_or_err(
                                self.program.as_deref_mut().unwrap(),
                                self.current_function,
                                "Renaming: No current function context found",
                            ),
                            phi.clone(),
                            k,
                            version,
                            Operand::BB(bb_id),
                        );
                    } else {
                        panic!(
                            "Renaming: no version available for variable {}, which means it is used before any store",
                            var_id
                        );
                    }
                } else {
                    panic!(
                        "Renaming: phi's variable not found in map, op_id: {}, op_map: {:?}",
                        op_id, self.op_to_var
                    );
                }
            }
        }

        // 3. Process children in domtree
        // Clone children list to avoid borrow
        let children = self.dom_trees[self.current_function.unwrap()][bb_id].clone();
        for child_id in children {
            self.rename(child_id);
        }

        // Restore the "frame pointer"
        for var in 0..self.versions.len() {
            let record = match self.records[var].pop() {
                Some(r) => r,
                None => panic!("Renaming: record stack underflow"),
            };
            self.versions[var].truncate(record);
        }
    }

    pub fn run(&mut self) {
        // remove load/store is done in rename

        let func_ids = self.program.as_ref().unwrap().funcs.collect_internal();
        for idx in func_ids {
            self.current_function = Some(idx);
            self.init();
            let head = {
                let func = &self.program.as_ref().unwrap().funcs[idx];
                match func.cfg.entry {
                    Some(id) => id,
                    None => continue,
                }
            };
            self.rename(head);

            // Clean up removed ops for this function
            let mut ctx = context_or_err(
                self.program.as_deref_mut().unwrap(),
                self.current_function,
                "Renaming: No current function context found",
            );
            for (op, bb) in &self.removed {
                self.builder
                    .remove_op(&mut ctx, op.clone(), Some(bb.clone()));
            }
            self.removed.clear();

            // Remove all the promoted allocas in entry block. You should do this after load/store removal, since some allocas might be used by dead load/store.
            let promoted_allocas = {
                let mut ctx = context_or_err(
                    self.program.as_deref_mut().unwrap(),
                    self.current_function,
                    "Renaming: No current function context found",
                );
                self.builder
                    .get_all_ops_in_block(&mut ctx, Operand::BB(head), OpType::Alloca)
                    .into_iter()
                    .filter(|alloca| {
                        let func = &self.program.as_ref().unwrap().funcs[idx];
                        let alloca_op = &func.dfg[alloca.clone()];
                        alloca_op
                            .attrs
                            .iter()
                            .any(|attr| matches!(attr, Attr::Promotion))
                    })
                    .collect::<Vec<Operand>>()
            };
            let mut ctx = context_or_err(
                self.program.as_deref_mut().unwrap(),
                self.current_function,
                "Renaming: No current function context found",
            );
            for alloca in promoted_allocas {
                self.builder
                    .remove_op(&mut ctx, alloca.clone(), Some(Operand::BB(head)));
            }
        }
    }
}

pub struct Mem2Reg<'a> {
    program: Option<&'a mut Program>,
}

impl<'a> Mem2Reg<'a> {
    pub fn new() -> Self {
        Self { program: None }
    }
}

impl<'a> Pass<'a> for Mem2Reg<'a> {
    fn name(&self) -> &str {
        "Mem2Reg"
    }
    fn set_program(&mut self, program: &'a mut Program) {
        self.program = Some(program);
    }
    fn run(&mut self) {
        let program = self.program.as_mut().unwrap();
        // 1. Build dominator tree
        info!("Start building dominator tree.");
        let mut dom_builder = BuildDomTree::new(program);
        let dom_trees = dom_builder.build();
        info!("Dominator tree built: {:?}", dom_trees);

        // 2. Build dominator frontier
        info!("Start building dominator frontier.");
        let mut df_builder = BuildDomFrontier::new(program, dom_trees.clone());
        let frontiers = df_builder.build();
        info!("Dominator frontier built: {:?}", frontiers);

        // 3. Insert Phi nodes
        info!("Start inserting phi nodes.");
        InsertPhi::new(program, frontiers).run();
        info!("Phi nodes inserted.");

        // 4. Rename variables
        info!("Start renaming variables.");
        let mut renamer = Renaming::new(program, dom_trees);
        renamer.run();
        info!("Variables renamed.");
    }
}
