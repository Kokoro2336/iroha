/// Utils for getting builder context from program and function index.
use crate::base::BuilderContext;
use crate::ir::mir::Program;

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
