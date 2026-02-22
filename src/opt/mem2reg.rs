/**
 * SSA construction & Mem2Reg based on Cytron et al. 1991's algorithm.
 * Reference: https://dl.acm.org/doi/pdf/10.1145/75277.75280
 */
use crate::base::ir::{Attr, Op, OpData, OpType, Operand, Program};
use crate::base::{context_or_err, Builder, BuilderContext, BuilderGuard, Pass, Type};
use crate::debug::info;
use crate::utils::bitset::BitSet;

use std::collections::HashMap;

macro_rules! acquire_cur_func_id {
    ($self:ident) => {
        match $self.current_function {
            Some(func_id) => func_id,
            None => panic!("No current function set"),
        }
    };
}

/**
 * Building dominator tree based on Lengauer-Tarjan algorithm.
 * Reference: https://dl.acm.org/doi/10.1145/357062.357071
 */
pub type DomTree = Vec<Vec<usize>>;
pub struct BuildDomTree<'a> {
    program: &'a mut Program,
    // Vertex number -> DFS number
    dfn: Vec<usize>,
    dfn_cnt: usize,
    // DFS number -> Vertex number
    rev: Vec<usize>,
    // Vertex number -> Semi-dominator DFS number
    sdom: Vec<usize>,
    // Vertex number -> vertices that this vertex semi-dominates
    bucket: Vec<Vec<usize>>,
    // Parent in DSU Forest
    parent: Vec<usize>,
    // Parent in the DFS Tree
    father: Vec<usize>,
    // Recording the vertex with the minimum semi-dominator on path sdom[u] -> u
    min: Vec<usize>,
    // Immediate dominator
    idom: Vec<usize>,

    // temp structure
    // Vertex number -> whether visited in DFS
    visited: BitSet,

    // state structure
    current_function: Option<usize>,

    // result
    dom_trees: Vec<DomTree>,
}

impl<'a> BuildDomTree<'a> {
    pub fn new(program: &'a mut Program) -> Self {
        let current_function = program.funcs.entry;
        Self {
            program,
            dfn: vec![],
            dfn_cnt: 0,
            rev: vec![],
            sdom: vec![],
            bucket: vec![],
            parent: vec![],
            father: vec![],
            min: vec![],
            idom: vec![],
            visited: BitSet::new(),
            current_function,
            dom_trees: vec![],
        }
    }

    fn init(&mut self, func: usize) {
        self.current_function = Some(func);
        let func = &self.program.funcs[func];

        let n = func.cfg.storage.len();
        self.dfn = vec![0; n];
        self.dfn_cnt = 0;

        self.rev = vec![0; n];

        self.bucket = vec![vec![]; n];
        self.father = vec![0; n];

        self.parent = (0..n).collect();
        self.sdom = (0..n).collect();
        self.idom = (0..n).collect();
        self.min = (0..n).collect();

        self.visited = BitSet::new();
    }

    fn dfs(&mut self, src: usize) {
        self.visited.insert(src);
        let dfs_num = self.dfn_cnt;
        self.dfn[src] = dfs_num;
        self.rev[dfs_num] = src;
        self.dfn_cnt += 1;

        let func_idx = acquire_cur_func_id!(self);

        let succs_len = {
            let func = &self.program.funcs[func_idx];
            let block = &func.cfg[src];
            block.succs.len()
        };

        (0..succs_len).for_each(|i| {
            let succ = {
                let func = &self.program.funcs[func_idx];
                let block = &func.cfg[src];
                match &block.succs[i] {
                    Operand::BB(id) => *id,
                    _ => panic!("BuildDomTree: successor is not a basic block"),
                }
            };
            if !self.visited.contains(succ) {
                self.father[succ] = src;
                self.dfs(succ);
            }
        })
    }

    fn find(&mut self, u: usize) -> usize {
        if self.parent[u] == u {
            return u;
        }
        let v = self.find(self.parent[u]);
        if self.dfn[self.sdom[self.min[u]]] > self.dfn[self.sdom[self.min[self.parent[u]]]] {
            self.min[u] = self.min[self.parent[u]];
        }
        self.parent[u] = v;
        self.parent[u]
    }

    fn query(&mut self, u: usize) -> usize {
        self.find(u);
        self.min[u]
    }

    fn dfn_min(&mut self, u: usize, v: usize) -> usize {
        if self.dfn[u] < self.dfn[v] {
            u
        } else {
            v
        }
    }

    pub fn build(&mut self) -> Vec<DomTree> {
        // Init dom trees first
        self.dom_trees = vec![vec![]; self.program.funcs.storage.len()];

        for idx in self.program.funcs.collect_internal() {
            let func = &self.program.funcs[idx];
            let head = match func.cfg.entry {
                Some(id) => id,
                None => continue,
            };

            self.init(idx);
            info!("Start DFS traversal.");
            self.dfs(head);

            info!("DFS traversal completed. Start computing dominators.");
            let num_visited = self.dfn_cnt;
            for i in (1..num_visited).rev() {
                let u = self.rev[i];

                let preds_num = {
                    let func = &self.program.funcs[acquire_cur_func_id!(self)];
                    let block = &func.cfg[u];
                    block.preds.len()
                };

                // find sdom[u]
                for idx in 0..preds_num {
                    let pred = {
                        let func = &self.program.funcs[acquire_cur_func_id!(self)];
                        let block = &func.cfg[u];
                        match &block.preds[idx] {
                            Operand::BB(id) => *id,
                            _ => continue,
                        }
                    };

                    if !self.visited.contains(pred) {
                        continue;
                    }

                    if self.dfn[pred] < self.dfn[u] {
                        self.sdom[u] = self.dfn_min(self.sdom[u], pred);
                    } else {
                        let v = self.query(pred);
                        self.sdom[u] = self.dfn_min(self.sdom[u], self.sdom[v]);
                    }
                }

                // push u to bucket of sdom[u]
                self.bucket[self.sdom[u]].push(u);

                // hang u to father[u] in DSU Forest
                self.parent[u] = self.father[u];

                // evaluate idom of vertices in bucket of father[u]
                // Emm... I have to use a clone due to the bothering borrow checker.
                let father = self.father[u];
                let bucket_len = self.bucket[father].len();
                for i in 0..bucket_len {
                    let v = self.bucket[father][i];
                    self.idom[v] = self.query(v);
                }
                self.bucket[father].clear();
            }

            // Refine idom
            info!("Dominator tree computed. Start refining immediate dominators.");
            for i in 0..self.rev.len() {
                let v = self.rev[i];
                let u = self.idom[v];
                // If sdom[u] != sdom[v], then there's a vertex with lower dfn that dominates v, which is idom[u],
                // so we set idom[v] to idom[u].
                // Otherwise, sdom[u] is the immediate dominator of v.
                if self.sdom[u] != self.sdom[v] {
                    self.idom[v] = self.idom[u];
                } else {
                    self.idom[v] = self.sdom[u];
                }
            }

            // export dom tree
            self.dom_trees[idx] = self.export();
        }
        std::mem::take(&mut self.dom_trees)
    }

    // FuncId -> DomTree
    pub fn export(&mut self) -> DomTree {
        let mut dom_tree = vec![vec![]; self.idom.len()];
        for idx in 0..self.idom.len() {
            let idom = self.idom[idx];
            if idom != idx {
                dom_tree[idom].push(idx);
            }
        }
        dom_tree
    }
}

pub type DomFrontier = Vec<Vec<usize>>;

pub struct BuildDomFrontier<'a> {
    program: &'a mut Program,
    dom_trees: Vec<DomTree>,
    // FuncId -> BlockId -> Frontier
    frontiers: Vec<DomFrontier>,
    // State field
    current_function: Option<usize>,
}

impl<'a> BuildDomFrontier<'a> {
    pub fn new(program: &'a mut Program, dom_trees: Vec<DomTree>) -> Self {
        Self {
            program,
            dom_trees,
            frontiers: vec![],
            current_function: None,
        }
    }

    pub fn init(&mut self, func_id: usize) {
        let func = &self.program.funcs[func_id];
        self.current_function = Some(func_id);
        self.frontiers[func_id] = vec![vec![]; func.cfg.storage.len()];
    }

    pub fn is_dom(&self, dominator: usize, dominatee: usize) -> bool {
        let func_id = acquire_cur_func_id!(self);

        let dom_num = {
            let dom_tree = &self.dom_trees[func_id];
            dom_tree[dominator].len()
        };
        if self.dom_trees[func_id][dominator].contains(&dominatee) {
            true
        } else {
            // If not direct child, check recursively
            (0..dom_num).any(|child| {
                let child = {
                    let dom_tree = &self.dom_trees[func_id];
                    dom_tree[dominator][child]
                };
                self.is_dom(child, dominatee)
            })
        }
    }

    pub fn compute(&mut self, bb_id: usize) {
        let func_id = acquire_cur_func_id!(self);

        let succs = {
            let func = &self.program.funcs[func_id];
            let block = &func.cfg[bb_id];
            let mut succs = Vec::new();
            for op in &block.succs {
                match op {
                    Operand::BB(id) => succs.push(*id),
                    _ => panic!("DomFrontier: successor is not a basic block"),
                }
            }
            succs
        };

        // Local frontier
        for succ in succs {
            if !self.is_dom(bb_id, succ) {
                self.frontiers[func_id][bb_id].push(succ);
            }
        }
        // Upward frontier
        let children_num = self.dom_trees[func_id][bb_id].len();
        for child_idx in 0..children_num {
            let child = self.dom_trees[func_id][bb_id][child_idx];
            self.compute(child);
            let child_frontier_len = self.frontiers[func_id][child].len();
            for i in 0..child_frontier_len {
                let w = self.frontiers[func_id][child][i];
                if !self.is_dom(bb_id, w) {
                    self.frontiers[func_id][bb_id].push(w);
                }
            }
        }
    }

    pub fn build(&mut self) -> Vec<DomFrontier> {
        // Init frontiers first
        self.frontiers = vec![vec![]; self.program.funcs.storage.len()];

        for idx in self.program.funcs.collect_internal() {
            let func = &self.program.funcs[idx];
            let head = match func.cfg.entry {
                Some(id) => id,
                None => continue,
            };
            self.init(idx);
            self.compute(head);
        }
        std::mem::take(&mut self.frontiers)
    }
}

pub struct InsertPhi<'a> {
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
            let mut ctx = context_or_err!(self, "InsertPhi: No current function context found");
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
        let func_id = acquire_cur_func_id!(self);
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
        let func_id = acquire_cur_func_id!(self);
        for idx in 0..defsites_len {
            while !self.defsites[idx].is_empty() {
                let bb_id = self.defsites[idx].pop().unwrap();

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
                        let guard = BuilderGuard::new(&self.builder);

                        self.builder.set_current_block(Operand::BB(frontier));

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

                        let mut ctx =
                            context_or_err!(self, "InsertPhi: No current function context found");
                        let phi_op_id = self.builder.create_at_head(
                            &mut ctx,
                            Op::new(
                                // We don't know the inst's result type yet
                                var_type,
                                vec![Attr::OldIdx(Operand::Value(self.var_to_op[&idx]))],
                                OpData::Phi {
                                    // Hold the place with dummy incoming. We will update it later.
                                    incoming: vec![(Operand::Value(0), Operand::BB(0)); preds_num],
                                },
                            ),
                        );

                        // Restore the old context
                        guard.restore(&mut self.builder);

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
                self.phi_ids.push(phi_ids);
            });
        std::mem::take(&mut self.phi_ids)
    }
}

pub struct Renaming<'a> {
    program: &'a mut Program,
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
            program,
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
            let func = &self.program.funcs[acquire_cur_func_id!(self)];
            let entry = match func.cfg.entry {
                Some(id) => id,
                None => panic!("Renaming: function has no entry block"),
            };
            let bbs = func.cfg.collect();
            (entry, bbs)
        };

        self.builder.set_current_block(Operand::BB(entry));
        let func_id = acquire_cur_func_id!(self);
        // For each block, we check if it contains an alloca. If it does, we move the alloca to the entry block.
        for bb_id in bbs {
            let allocas = {
                let mut ctx = context_or_err!(self, "Renaming: No current function context found");
                self.builder
                    .get_all_ops_in_block(&mut ctx, Operand::BB(bb_id), OpType::Alloca)
            };

            // Filter allocas that are not promoted (e.g., those without the Promotion attribute). We won't promote them, so we can just ignore them in renaming.
            let promoted_allocas: Vec<Operand> = allocas
                .into_iter()
                .filter(|alloca| {
                    let func = &self.program.funcs[func_id];
                    let alloca_op = &func.dfg[alloca.clone()];
                    alloca_op
                        .attrs
                        .iter()
                        .any(|attr| matches!(attr, Attr::Promotion))
                })
                .collect();

            let mut ctx = context_or_err!(self, "Renaming: No current function context found");

            // Initialize the map between OpId and VarId
            for alloca in promoted_allocas {
                let op_id = match alloca {
                    Operand::Value(id) => id,
                    _ => panic!("Renaming: allocas contains non-op"),
                };

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
            let func = &self.program.funcs[acquire_cur_func_id!(self)];
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
                let func = &self.program.funcs[acquire_cur_func_id!(self)];
                let op = &func.dfg[inst.clone()];
                (op.data.clone(), op.attrs.clone())
            };

            match op_data {
                OpData::Store { addr, value } => {
                    match addr {
                        Operand::Value(_) => {},
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
                        Operand::Value(_) => {},
                        // We won't promote global variables.
                        Operand::Global(_) => continue,
                        _ => panic!("Renaming: store address is not a value or global"),
                    };

                    if let Some(&var_id) = self.op_to_var.get(&addr.get_op_id()) {
                        if let Some(version) = self.versions[var_id].last() {
                            // Replace the load with the current version
                            let new_val = version.clone();
                            let mut ctx = context_or_err!(
                                self,
                                "Renaming: No current function context found"
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
                let func = &self.program.funcs[acquire_cur_func_id!(self)];
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
                let mut ctx = context_or_err!(self, "Renaming: No current function context found");
                self.builder
                    .get_all_ops_in_block(&mut ctx, succ.clone(), OpType::Phi)
            };

            for phi in phis {
                // Check if this phi is one we track (has a var_id)
                // Update phi incoming
                let op_id = {
                    let func = &self.program.funcs[acquire_cur_func_id!(self)];
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
                            &mut context_or_err!(
                                self,
                                "Renaming: No current function context found"
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
        let children = self.dom_trees[acquire_cur_func_id!(self)][bb_id].clone();
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

        for idx in self.program.funcs.collect_internal() {
            self.current_function = Some(idx);
            self.init();
            let head = {
                let func = &self.program.funcs[idx];
                match func.cfg.entry {
                    Some(id) => id,
                    None => continue,
                }
            };
            self.rename(head);

            // Clean up removed ops for this function
            let mut ctx = context_or_err!(self, "Renaming: No current function context found");
            for (op, bb) in &self.removed {
                self.builder.remove_op(&mut ctx, op.clone(), bb.clone());
            }
            self.removed.clear();
        }
    }
}

pub struct RemoveTrivialPhi<'a> {
    program: &'a mut Program,
    builder: Builder,
    phi_ids: Vec<Vec<(Operand, Operand)>>,

    // Ancillary state fields
    worklist: Vec<(Operand, Operand)>,

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

    pub fn remove(&mut self, idx: usize) {
        self.current_function = Some(idx);
        self.worklist = self.phi_ids[idx].clone();

        enum CheckType {
            Empty,
            Single(Operand), // (OpId, BBId)
            Multiple,
        }
        fn check(ctx: &mut BuilderContext, phi: Operand) -> CheckType {
            let dfg = ctx.dfg.as_ref().unwrap();
            let phi_op = &dfg[phi.clone()];
            match &phi_op.data {
                OpData::Phi { incoming } => {
                    let mut distinct: Vec<(Operand, Operand)> = vec![];
                    for (value, bb_id) in incoming.iter() {
                        if matches!(value, Operand::Undefined) || *value == phi {
                            continue;
                        }

                        if distinct.iter().all(|(v, _)| *v != *value) {
                            distinct.push((value.clone(), bb_id.clone()));
                            if distinct.len() > 1 {
                                return CheckType::Multiple;
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
                _ => panic!("RemoveTrivialPhi: expected phi op"),
            }
        }

        // Check whether the phi_ids are valid
        while let Some((phi_id, bb_id)) = self.worklist.pop() {
            let uses = {
                let func = &self.program.funcs[acquire_cur_func_id!(self)];
                func.dfg[phi_id.clone()].users.clone()
            };
            let mut ctx =
                context_or_err!(self, "RemoveTrivialPhi: No current function context found");
            match check(&mut ctx, phi_id.clone()) {
                CheckType::Empty => {
                    self.builder
                        .replace_all_uses(&mut ctx, phi_id.clone(), Operand::Undefined);
                    for user in uses {
                        if matches!(
                            check(&mut ctx, user.clone()),
                            CheckType::Empty | CheckType::Single(_)
                        ) {
                            self.worklist.push((user, bb_id.clone()));
                        }
                    }
                    self.builder.remove_op(&mut ctx, phi_id, bb_id);
                }
                CheckType::Single(value) => {
                    self.builder
                        .replace_all_uses(&mut ctx, phi_id.clone(), value);
                    for user in uses {
                        if matches!(
                            check(&mut ctx, user.clone()),
                            CheckType::Empty | CheckType::Single(_)
                        ) {
                            self.worklist.push((user, bb_id.clone()));
                        }
                    }
                    self.builder.remove_op(&mut ctx, phi_id, bb_id);
                }
                CheckType::Multiple => {}
            }
        }
    }

    pub fn run(&mut self) {
        for idx in self.program.funcs.collect_internal() {
            self.remove(idx);
        }
    }
}

pub struct Mem2Reg {
    program: Program,
}

impl Mem2Reg {
    pub fn new(program: Program) -> Self {
        Self { program }
    }
}

impl Pass<Program> for Mem2Reg {
    fn run(&mut self) -> Program {
        // 1. Build dominator tree
        info!("Start building dominator tree.");
        let mut dom_builder = BuildDomTree::new(&mut self.program);
        let dom_trees = dom_builder.build();
        info!("Dominator tree built: {:?}", dom_trees);

        // 2. Build dominator frontier
        info!("Start building dominator frontier.");
        let mut df_builder = BuildDomFrontier::new(&mut self.program, dom_trees.clone());
        let frontiers = df_builder.build();
        info!("Dominator frontier built: {:?}", frontiers);

        // 3. Insert Phi nodes
        info!("Start inserting phi nodes.");
        let mut phi_inserter = InsertPhi::new(&mut self.program, frontiers);
        let phi_ids = phi_inserter.run();
        info!("Phi nodes inserted.");

        // 4. Rename variables
        info!("Start renaming variables.");
        let mut renamer = Renaming::new(&mut self.program, dom_trees);
        renamer.run();
        info!("Variables renamed.");

        // 5. Remove trivial phi nodes
        info!("Start removing trivial phi nodes.");
        let mut remover = RemoveTrivialPhi::new(&mut self.program, phi_ids);
        remover.run();
        info!("Trivial phi nodes removed.");

        std::mem::take(&mut self.program)
    }
}
