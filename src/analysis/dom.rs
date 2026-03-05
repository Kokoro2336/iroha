use crate::debug::info;
/// Building dominator tree based on Lengauer-Tarjan algorithm.
/// Reference: https://dl.acm.org/doi/10.1145/357062.357071
use crate::ir::mir::{Operand, Program};
use crate::utils::bitset::BitSet;

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

        let func_idx = self.current_function.unwrap();

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
                    let func = &self.program.funcs[self.current_function.unwrap()];
                    let block = &func.cfg[u];
                    block.preds.len()
                };

                // find sdom[u]
                for idx in 0..preds_num {
                    let pred = {
                        let func = &self.program.funcs[self.current_function.unwrap()];
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
        let func_id = self.current_function.unwrap();

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
        let func_id = self.current_function.unwrap();

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
