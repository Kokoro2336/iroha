use std::collections::HashMap;

pub trait Pass<T> {
    fn run(&mut self) -> T;
}

pub struct SymbolTable<T, U> {
    tables: Vec<HashMap<T, U>>,
}

impl<T: std::hash::Hash + Eq, U> SymbolTable<T, U> {
    pub fn new() -> Self {
        SymbolTable {
            tables: vec![],
        }
    }

    pub fn enter_scope(&mut self) {
        self.tables.push(HashMap::new());
    }

    pub fn exit_scope(&mut self) {
        if self.tables.pop().is_none() {
            panic!("No scope to exit");
        };
    }

    pub fn insert(&mut self, key: T, value: U) {
        self.tables.last_mut().unwrap().insert(key, value);
    }

    pub fn get(&self, key: &T) -> Option<&U> {
        for table in self.tables.iter().rev() {
            if let Some(value) = table.get(key) {
                return Some(value);
            }
        }
        None
    }
    
    pub fn current_scope(&self) -> usize {
        self.tables.len()
    }
}

macro_rules! context {
    ($self:ident) => {
        if let Some(func_idx) = $self.current_function {
            let func = &mut $self.program.funcs[func_idx];
            BuilderContext {
                cfg: Some(&mut func.cfg),
                dfg: Some(&mut func.dfg),
                globals: &mut $self.program.globals,
            }
        } else {
            BuilderContext {
                cfg: None,
                dfg: None,
                globals: &mut $self.program.globals,
            }
        }
    };
}

macro_rules! context_or_err {
    ($self:ident, $msg:expr) => {
        if let Some(func_idx) = $self.current_function {
            let func = &mut $self.program.funcs[func_idx];
            BuilderContext {
                cfg: Some(&mut func.cfg),
                dfg: Some(&mut func.dfg),
                globals: &mut $self.program.globals,
            }
        } else {
            panic!($msg);
        }
    };
}

pub(crate) use {context, context_or_err};

