/// Simplify CFG.
use crate::base::ir::{Program};

pub struct SimplifyCFG<'a> {
    pub program: &'a mut Program,
}

impl<'a> SimplifyCFG<'a> {
    pub fn new(program: &'a mut Program) -> Self {
        Self { program }
    }
}
