use crate::base::Pass;
use crate::ir::mir::Program;
use crate::utils::arena::Arena;

pub struct Compaction<'a> {
    program: Option<&'a mut Program>,
}

impl<'a> Compaction<'a> {
    pub fn new() -> Self {
        Self { program: None }
    }
}

impl<'a> Pass<'a> for Compaction<'a> {
    fn name(&self) -> &str {
        "Compaction"
    }
    fn set_program(&mut self, ir: &'a mut Program) {
        self.program = Some(ir);
    }
    fn run(&mut self) {
        self.program.as_mut().unwrap().funcs.gc();
    }
}
