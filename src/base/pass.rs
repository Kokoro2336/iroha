use crate::base::BuilderContext;
use crate::debug::info;
use crate::debug::DumpLLVM;
use crate::ir::mir::Program;

use crate::cli::Cli;
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
    cli: &'a Cli,
}

impl<'a> PassManager<'a> {
    pub fn new(cli: &'a Cli) -> Self {
        PassManager {
            passes: VecDeque::new(),
            cli,
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

            if self.cli.emit_llvm && self.cli.dump_after == pass.name() {
                info!("Dumping IR after pass: {}", pass.name());
                let filename = self
                    .cli
                    .input
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("output")
                    .to_string();
                unsafe {
                    DumpLLVM::new(&mut *ir_ptr, filename).run();
                }
                info!("Finished dumping IR after pass: {}", pass.name());
                info!("Quit after dumping.");
                std::process::exit(0)
            }
        }

        // If no pass specified, dump the LLVM IR after all optimizations.
        if self.cli.emit_llvm && self.cli.dump_after.is_empty() {
            info!("Start Dumping LLVM IR.");
            let filename = self
                .cli
                .input
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("output")
                .to_string();
            unsafe {
                DumpLLVM::new(&mut *ir_ptr, filename).run();
            }
            info!("Finish Dumping LLVM IR.");
            info!("Quit after dumping.");
            std::process::exit(0)
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
