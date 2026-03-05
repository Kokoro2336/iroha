/// A simple symbol table implementation using a stack of hash maps to represent scopes.
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

pub struct SymbolTable<T, U> {
    tables: Vec<HashMap<T, U>>,
}

impl<T: std::hash::Hash + Eq, U> SymbolTable<T, U> {
    pub fn new() -> Self {
        SymbolTable { tables: vec![] }
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

#[allow(unused)]
pub struct ScopeGuard<'a, T: std::hash::Hash + Eq, U> {
    symbol_table: &'a mut SymbolTable<T, U>,
}

#[allow(unused)]
impl<'a, T: std::hash::Hash + Eq, U> ScopeGuard<'a, T, U> {
    pub fn new(symbol_table: &'a mut SymbolTable<T, U>) -> Self {
        symbol_table.enter_scope();
        ScopeGuard { symbol_table }
    }
}

impl<'a, T: std::hash::Hash + Eq, U> Drop for ScopeGuard<'a, T, U> {
    fn drop(&mut self) {
        self.symbol_table.exit_scope();
    }
}

impl<'a, T: std::hash::Hash + Eq, U> Deref for ScopeGuard<'a, T, U> {
    type Target = SymbolTable<T, U>;

    fn deref(&self) -> &Self::Target {
        self.symbol_table
    }
}

impl<'a, T: std::hash::Hash + Eq, U> DerefMut for ScopeGuard<'a, T, U> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.symbol_table
    }
}
