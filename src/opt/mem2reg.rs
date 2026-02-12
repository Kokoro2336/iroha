use crate::base::ir::{Attr, Op, OpData, OpType, Operand, Program};
use crate::base::{Builder, BuilderGuard, BuilderContext, Type, Pass};
use crate::frontend::context_or_err;
use crate::utils::bitset::BitSet;

use std::collections::HashMap;

macro_rules! acquire_cur_func_id {
    ($self:ident) => {
        match $self.current_function {
            Some(func_id) => func_id,
            None => return Err("No current function set".to_string()),
        }
    };
}

macro_rules! validate_func {
    ($self:ident, $func_id:ident) => {
        if $self.program.funcs.get($func_id)?.is_none() {
            return Err("Function not found".to_string());
        }
    };
}

/**
 * Building dominator tree based on Lengauer-Tarjan algorithm.
 * Reference: https://dl.acm.org/toc/toplas/1979/1/1
 */
pub type DomTree = Vec<Vec<usize>>;
pub struct BuildDomTree<'a> {
    program: &'a mut Program,
    // Vertex number -> DFS number
    dfn: Vec<usize>,
    // DFS number -> Vertex number
    rev: Vec<usize>,
    // Vertex number -> Semi-dominator
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
        let current_function = program.funcs.entry.clone();
        Self {
            program,
            // Take the 0th index as counter
            dfn: vec![1],
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

    fn init(&mut self, func: usize) -> Result<(), String> {
        self.current_function = Some(func);
        let func = &self.program.funcs[func];

        self.dfn = vec![0; func.cfg.storage.len()];
        self.dfn[0] = 1;

        // Initialize sdom to 0, which is greater than the max DFS number.
        self.sdom = vec![0; func.cfg.storage.len()];

        self.rev = vec![0; func.cfg.storage.len()];
        self.bucket = vec![vec![]; func.cfg.storage.len()];
        self.father = vec![0; func.cfg.storage.len()];

        self.parent = (0..func.cfg.storage.len()).collect();
        self.idom = (0..func.cfg.storage.len()).collect();
        self.min = (0..func.cfg.storage.len()).collect();

        self.visited = BitSet::new();
        self.current_function = None;
        Ok(())
    }

    fn dfs(&mut self, src: usize) -> Result<(), String> {
        self.visited.insert(src);
        self.dfn[src] = self.dfn[0];
        self.dfn[0] += 1;
        self.rev.push(src);

        let func_idx = acquire_cur_func_id!(self);

        let succs_len = {
            let func = &self.program.funcs[func_idx];
            let block = &func.cfg[src];
            block.succs.len()
        };

        (0..succs_len).try_for_each(|i| {
            let succ = {
                let func = &self.program.funcs[func_idx];
                let block = &func.cfg[src];
                match &block.succs[i] {
                    Operand::BB(id) => *id,
                    _ => return Err("BuildDomTree: successor is not a basic block".to_string()),
                }
            };
            if !self.visited.contains(succ) {
                self.father[succ] = src;
                self.dfs(succ)?;
            }
            Ok(())
        })
    }

    fn query(&mut self, u: usize) -> usize {
        if self.parent[u] == u {
            return u;
        }
        let v = self.query(self.parent[u]);
        if self.dfn[self.sdom[self.min[u]]] > self.dfn[self.sdom[self.min[self.parent[u]]]] {
            self.min[u] = self.min[self.parent[u]];
        }
        self.parent[u] = v;
        self.min[u]
    }

    fn dfn_min(&mut self, u: usize, v: usize) -> usize {
        if self.dfn[u] < self.dfn[v] {
            u
        } else {
            v
        }
    }

    pub fn build(&mut self) -> Result<Vec<DomTree>, String> {
        // Init dom trees first
        self.dom_trees = vec![vec![]; self.program.funcs.storage.len()];

        for idx in (0..self.program.funcs.storage.len()) {
            validate_func!(self, idx);
            let func = &self.program.funcs[idx];
            let head = match func.cfg.entry {
                Some(id) => id,
                None => continue,
            };

            self.init(idx)?;
            self.dfs(head)?;

            for i in (1..self.rev.len()).rev() {
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

                    if self.dfn[pred] < self.dfn[u] {
                        self.sdom[u] = self.dfn_min(self.sdom[u], pred);
                    } else {
                        let v = self.query(pred);
                        self.sdom[u] = self.dfn_min(self.sdom[u], self.sdom[v]);
                    }
                }
                // push u to bucket of sdom[u]
                self.bucket[self.sdom[u]].push(u);

                // evaluate idom of vertices in bucket of father[u]
                let father = self.father[u];
                // Emm... I have to use a clone due to the bothering borrow checker.
                let bucket_len = self.bucket[father].len();
                for i in 0..bucket_len {
                    let v = self.bucket[father][i];
                    let w = self.query(v);
                    if self.dfn[self.sdom[w]] < self.dfn[self.sdom[v]] {
                        self.idom[v] = w;
                    } else {
                        self.idom[v] = father;
                    }
                }
                self.bucket[father].clear();

                // hang u to father[u] in DSU Forest
                self.parent[father] = father;
            }

            // Refine idom
            for i in 1..self.rev.len() {
                let v = self.rev[i];
                let u = self.idom[v];
                self.idom[v] = self.dfn_min(u, self.idom[u]);
            }

            // export dom tree
            self.dom_trees[idx] = self.export();
        }
        Ok(std::mem::take(&mut self.dom_trees))
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

    pub fn init(&mut self, func_id: usize) -> Result<(), String> {
        let func = &self.program.funcs[func_id];
        self.current_function = Some(func_id);
        self.frontiers[func_id] = vec![vec![]; func.cfg.storage.len()];
        Ok(())
    }

    pub fn is_dom(&self, dominator: usize, dominatee: usize) -> Result<bool, String> {
        let func_id = acquire_cur_func_id!(self);

        let dom_num = {
            let dom_tree = &self.dom_trees[func_id];
            dom_tree[dominator].len()
        };
        Ok(if self.dom_trees[func_id][dominator].contains(&dominatee) {
            true
        } else {
            // If not direct child, check recursively
            (0..dom_num).any(|child| {
                let child = {
                    let dom_tree = &self.dom_trees[func_id];
                    dom_tree[dominator][child]
                };
                self.is_dom(child, dominatee).unwrap_or(false)
            })
        })
    }

    pub fn compute(&mut self, bb_id: usize) -> Result<(), String> {
        let func_id = acquire_cur_func_id!(self);

        let succs = {
            let func = &self.program.funcs[func_id];
            let block = &func.cfg[bb_id];
            let mut succs = Vec::new();
            for op in &block.succs {
                match op {
                    Operand::BB(id) => succs.push(*id),
                    _ => return Err("DomFrontier: successor is not a basic block".to_string()),
                }
            }
            succs
        };

        // Local frontier
        for succ in succs {
            if !self.is_dom(bb_id, succ)? {
                self.frontiers[func_id][bb_id].push(succ);
            }
        }
        // Upward frontier
        let children_num = self.dom_trees[func_id][bb_id].len();
        for child_idx in 0..children_num {
            let child = self.dom_trees[func_id][bb_id][child_idx];
            self.compute(child)?;
            let child_frontier_len = self.frontiers[func_id][child].len();
            for i in 0..child_frontier_len {
                let w = self.frontiers[func_id][child][i];
                if !self.is_dom(bb_id, w)? {
                    self.frontiers[func_id][bb_id].push(w);
                }
            }
        }
        Ok(())
    }

    pub fn build(&mut self) -> Result<Vec<DomFrontier>, String> {
        // Init frontiers first
        self.frontiers = vec![vec![]; self.program.funcs.storage.len()];

        for idx in 0..self.program.funcs.storage.len() {
            validate_func!(self, idx);
            let func = &self.program.funcs[idx];
            let head = match func.cfg.entry {
                Some(id) => id,
                None => continue,
            };
            self.init(idx)?;
            self.compute(head)?;
        }
        Ok(std::mem::take(&mut self.frontiers))
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
        }
    }

    pub fn init(&mut self) -> Result<(), String> {
        self.op_to_var.clear();
        self.var_to_op.clear();
        self.var_counter = 0;

        let func = &self.program.funcs[acquire_cur_func_id!(self)];
        let allocas = self.builder.get_all_ops(
            context_or_err!(
                self,
                "InsertPhi: No current function context found".to_string()
            ),
            OpType::Alloca,
        );

        // Initialize the map between OpId and VarId
        for alloca in allocas.into_iter() {
            let op_id = match alloca {
                Operand::Value(id) => id,
                _ => return Err("InsertPhi: allocas contains non-op".to_string()),
            };
            let var_id = self.var_counter;
            self.var_counter += 1;

            self.op_to_var.insert(op_id, var_id);
            self.var_to_op.insert(var_id, op_id);
        }

        self.defsites = Vec::with_capacity(self.var_counter);
        self.origins = Vec::with_capacity(func.cfg.storage.len());
        self.phis = Vec::with_capacity(self.var_counter);

        // Compute defsites, origins and phis
        (0..func.cfg.storage.len()).try_for_each(|bb_id| {
            let block = &func.cfg[bb_id];
            block.cur.iter().try_for_each(|op_id| {
                let op_id = match op_id {
                    Operand::Value(id) => *id,
                    _ => return Err("InsertPhi: cur contains non-op".to_string()),
                };

                let op = &func.dfg[op_id];
                if op.is(OpType::Store) {
                    let var_id = self.op_to_var[&op_id];
                    self.defsites[var_id].push(bb_id);
                    self.origins[bb_id].push(var_id);
                }
                Ok(())
            })
        })?;

        Ok(())
    }

    pub fn insert(&mut self) -> Result<(), String> {
        (0..self.defsites.len()).try_for_each(|idx| {
            while !self.defsites[idx].is_empty() {
                let defsite = &mut self.defsites[idx];
                let bb_id = match defsite.pop() {
                    Some(id) => id,
                    None => break,
                };

                let frontiers = &self.frontiers[acquire_cur_func_id!(self)][bb_id];
                for frontier in frontiers {
                    // If the phi already exists, we don't need to insert it again, but we still need to update the origins.
                    if !self.phis[idx].contains(frontier) {
                        // Insert phi
                        // Use guard to save the old context
                        let _guard = BuilderGuard::new(&mut self.builder);

                        self.builder.set_current_block(Operand::BB(bb_id))?;
                        self.builder.create_at_head(
                            context_or_err!(self, "InsertPhi: No current function context found"),
                            Op::new(
                                // We don't know the inst's result type yet
                                Type::Void,
                                vec![Attr::OldIdx(Operand::Value(self.var_to_op[&idx]))],
                                // We don't know the incoming values yet
                                OpData::Phi { incoming: vec![] },
                            ),
                        )?;

                        self.phis[idx].push(*frontier);
                        if !self.origins[*frontier].contains(&idx) {
                            // If it is a new definition in the frontier block, we add the block to the var's worklist.
                            self.defsites[idx].push(*frontier);
                        }
                    }
                }
            }
            Ok(())
        })?;
        Ok(())
    }

    pub fn run(&mut self) -> Result<(), String> {
        (0..self.program.funcs.storage.len()).try_for_each(|idx| -> Result<(), String> {
            self.current_function = Some(idx);
            self.init()?;
            self.insert()?;
            Ok(())
        })?;
        Ok(())
    }
}

pub struct Renaming<'a> {
    program: &'a mut Program,
    builder: Builder,
    dom_trees: Vec<DomTree>,
    // Record the previous "frame pointer" of the version stack
    records: Vec<Vec<usize>>,
    // version stack
    versions: Vec<Vec<usize>>,

    // State field
    current_function: Option<usize>,

    // Temporary map from VarId to OpId to avoid sparse indexing of the above structures
    op_to_var: HashMap<usize, usize>,
    var_to_op: HashMap<usize, usize>,
    var_counter: usize,

    // The old load/store that need to be removed
    removed: Vec<Operand>,
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

    fn init(&mut self) -> Result<(), String> {
        self.op_to_var.clear();
        self.var_to_op.clear();
        self.var_counter = 0;

        let func = &self.program.funcs[acquire_cur_func_id!(self)];
        let allocas = self.builder.get_all_ops(
            context_or_err!(
                self,
                "InsertPhi: No current function context found".to_string()
            ),
            OpType::Alloca,
        );

        // Initialize the map between OpId and VarId
        for alloca in allocas.into_iter() {
            let op_id = match alloca {
                Operand::Value(id) => id,
                _ => return Err("Renaming: allocas contains non-op".to_string()),
            };
            let var_id = self.var_counter;
            self.var_counter += 1;

            self.op_to_var.insert(op_id, var_id);
            self.var_to_op.insert(var_id, op_id);
        }

        self.records = Vec::with_capacity(self.var_counter);
        self.versions = Vec::with_capacity(self.var_counter);
        Ok(())
    }

    fn rename(&mut self, bb_id: usize) -> Result<(), String> {
        // Record current "frame pointer"
        for var in 0..self.versions.len() {
            self.records[var].push(self.versions[var].len());
        }
        let bb = &self.program.funcs[acquire_cur_func_id!(self)].cfg[bb_id];
        for inst in bb.cur.iter() {
            let op_id = match inst {
                Operand::Value(id) => *id,
                _ => return Err("Renaming: cur contains non-op".to_string()),
            };
            let op = &self.program.funcs[acquire_cur_func_id!(self)].dfg[op_id];
            if op.is(OpType::Store) {
                let var_id = self.op_to_var[&op_id];
                self.versions[var_id].push(op_id);
                self.removed.push(Operand::Value(op_id));
            } else if op.is(OpType::Load) {
                let var_id = self.op_to_var[&op_id];
                if let Some(version) = self.versions[var_id].last() {
                    // Replace the load with the current version
                    let new_op_id = *version;
                    self.builder.replace_all_uses(
                        context_or_err!(
                            self,
                            "Renaming: No current function context found".to_string()
                        ),
                        Operand::Value(op_id),
                        Operand::Value(new_op_id),
                    )?;
                    self.removed.push(Operand::Value(op_id));
                } else {
                    return Err(format!(
                        "Renaming: load from variable {} before any store",
                        var_id
                    ));
                }
            } else if op.is(OpType::Phi) {
                let var_id = self.op_to_var[&op_id];
                self.versions[var_id].push(op_id);
            }
        }

        // Processing succs
        for succ in &bb.succs {
            let succ_id = match succ {
                Operand::BB(id) => *id,
                _ => return Err("Renaming: successor is not a basic block".to_string()),
            };
            let succ_block = &self.program.funcs[acquire_cur_func_id!(self)].cfg[succ_id];
            // Replace the k'th incoming block with the current version
            let k = succ_block
                .preds
                .iter()
                .position(|pred| match pred {
                    Operand::BB(id) => *id == bb_id,
                    _ => false,
                })
                .ok_or_else(|| {
                    "Renaming: predecessor not found in successor's preds".to_string()
                })?;
            // Find all the phis
            let phis = self.builder.get_all_ops_in_block(
                context_or_err!(self, "No context available"),
                succ.clone(),
                OpType::Phi,
            )?;
            for phi in phis {
                let phi_id = match phi {
                    Operand::Value(id) => id,
                    _ => return Err("Renaming: phi contains non-op".to_string()),
                };
                let phi_op = &mut self.program.funcs[acquire_cur_func_id!(self)].dfg[phi_id];
                match &mut phi_op.data {
                    OpData::Phi { incoming } => {
                        let var_id = self.op_to_var[&phi_id];
                        if let Some(version) = self.versions[var_id].last() {
                            // Replace the k'th incoming block with the current version
                            incoming[k] = (Operand::Value(*version), Operand::BB(bb_id));
                        } else {
                            return Err(format!(
                                "Renaming: phi operand from variable {} before any store",
                                var_id
                            ));
                        }
                    }
                    _ => return Err("Renaming: expected phi op".to_string()),
                }
            }
        }

        // Processing children in domtree
        for child in &self.dom_trees[acquire_cur_func_id!(self)][bb_id] {
            self.rename(*child)?;
        }

        // Restore the "frame pointer"
        for var in 0..self.versions.len() {
            let record = match self.records[var].pop() {
                Some(r) => r,
                None => return Err("Renaming: record stack underflow".to_string()),
            };
            self.versions[var].truncate(record);
        }

        // remove the load/store
        for op in &self.removed {
            let op_id = match op {
                Operand::Value(id) => *id,
                _ => return Err("Renaming: removed contains non-op".to_string()),
            };
            self.builder.remove_op(Operand::Value(op_id))?;
        }
        Ok(())
    }

    pub fn run(&mut self) -> Result<(), String> {
        for idx in 0..self.program.funcs.storage.len() {
            validate_func!(self, idx);
            self.current_function = Some(idx);
            self.init()?;
            let head = {
                let func = &self.program.funcs[idx];
                match func.cfg.entry {
                    Some(id) => id,
                    None => continue,
                }
            };
            self.rename(head)?;
        }
        // TODO: Compact field incoming in phi ops to eliminate the redundant placeholders
        Ok(())
    }
}

pub struct Mem2Reg<'a> {
    program: &'a mut Program,
}

impl<'a> Pass<()> for Mem2Reg<'a> {
    fn run(&mut self) -> Result<(), String> {
        let dom_trees = BuildDomTree::new(self.program).build()?;
        let dom_frontiers = BuildDomFrontier::new(self.program, dom_trees.clone()).build()?;
        InsertPhi::new(self.program, dom_frontiers).run()?;
        Renaming::new(self.program, dom_trees).run()?;
        Ok(())
    }
}
