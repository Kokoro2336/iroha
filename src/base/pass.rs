use std::collections::HashMap;

pub trait Pass<T> {
    fn run(&mut self) -> Result<T, String>;
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
}
