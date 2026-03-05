use crate::ir::mir::{CG, DFG};

#[derive(Debug, Clone)]
pub struct Program {
    // Including:
    // 1. global variables
    // 2. SysY library functions
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
