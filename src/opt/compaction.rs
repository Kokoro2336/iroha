use crate::base::ir::Program;
use crate::base::Pass;
use crate::utils::arena::Arena;

pub struct Compaction<'a> {
    program: &'a mut Program,
}

impl<'a> Compaction<'a> {
    pub fn new(program: &'a mut Program) -> Self {
        Self { program }
    }
}

impl<'a> Pass<()> for Compaction<'a> {
    fn run(&mut self) {
        self.program.funcs.gc();
    }
}
