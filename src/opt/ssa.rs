use crate::base::ir::{Function, Program, Operand};
use crate::base::Pass;
use crate::utils::bitset::BitSet;

pub type DomTree = Vec<Vec<usize>>;

/**
 * Building dominator tree based on Lengauer-Tarjan algorithm.
 * Reference: https://dl.acm.org/toc/toplas/1979/1/1
 */
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
        }
    }

    // Clear all data structures
    fn clear(&mut self) {
        self.dfn.clear();
        self.dfn.push(1);
        self.rev.clear();
        self.sdom.clear();
        self.bucket.clear();
        self.parent.clear();
        self.father.clear();
        self.min.clear();
        self.idom.clear();
        self.visited.clear();
        self.current_function = None;
    }

    fn init(&mut self, func: usize) {
        todo!()
    }

    fn dfs(&mut self, src: usize) -> Result<(), String> {
        self.visited.insert(src);
        self.dfn[src] = self.dfn[0];
        self.dfn[0] += 1;
        self.rev.push(src);

        let succs = {
            let func = &self.program.funcs[self.current_function.unwrap()];
            let block = &func.cfg[src];
            block.succs.clone()
        };

        succs.iter().try_for_each(|succ| {
            let succ = match succ {
                Operand::BB(id) => *id,
                _ => return Err("BuildDomTree: successor is not a basic block".to_string()),
            };
            if !self.visited.contains(succ) {
                self.father.push(src);
                self.dfs(succ)?;
            }
            Ok(())
        })
    }

    pub fn build(&mut self) {
        todo!()
    }
}
