use crate::base::BuilderContext;
use crate::debug::info;
use crate::ir::mir::Program;

use std::collections::VecDeque;

pub trait Pass<'a> {
    fn name(&self) -> &str;
    fn set_program(&mut self, program: &'a mut Program);
    fn run(&mut self);
}

pub struct PassManager<'a> {
    // The lifetime 'a is tied to the Program that the passes will operate on.
    // The `+ 'a` bound is necessary because the passes themselves (like DCE<'a>)
    // contain a mutable reference to the Program with lifetime 'a.
    passes: VecDeque<Box<dyn Pass<'a> + 'a>>,
}

impl<'a> PassManager<'a> {
    pub fn new() -> Self {
        PassManager {
            passes: VecDeque::new(),
        }
    }

    pub fn register(mut self, pass: Box<dyn Pass<'a> + 'a>) -> Self {
        self.passes.push_back(pass);
        self
    }

    pub fn run(mut self, ir: &'a mut Program) {
        let ir_ptr: *mut Program = ir;
        while let Some(mut pass) = self.passes.pop_front() {
            info!("Running pass: {}", pass.name());
            // SAFETY: Passes run sequentially and each pass only borrows `ir` during this iteration.
            unsafe { pass.set_program(&mut *ir_ptr) };
            pass.run();
            info!("Finished pass: {}", pass.name());
        }
    }
}

pub fn context_or_err<'a>(
    program: &'a mut Program,
    idx: Option<usize>,
    msg: &str,
) -> BuilderContext<'a> {
    if let Some(func_idx) = idx {
        let (funcs, globals) = (&mut program.funcs, &mut program.globals);
        let func = &mut funcs[func_idx];
        BuilderContext {
            cfg: Some(&mut func.cfg),
            dfg: Some(&mut func.dfg),
            globals,
        }
    } else {
        panic!("{}", msg);
    }
}

pub fn context<'a>(program: &'a mut Program, idx: Option<usize>) -> BuilderContext<'a> {
    if let Some(func_idx) = idx {
        let (funcs, globals) = (&mut program.funcs, &mut program.globals);
        let func = &mut funcs[func_idx];
        BuilderContext {
            cfg: Some(&mut func.cfg),
            dfg: Some(&mut func.dfg),
            globals,
        }
    } else {
        BuilderContext {
            cfg: None,
            dfg: None,
            globals: &mut program.globals,
        }
    }
}
