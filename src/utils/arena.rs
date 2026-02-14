/**
 * Simple arena allocator for indexed storage of values.
 * Faster retrieval by index compared to HashMap.
 */
use std::collections::HashMap;
use std::ops::{Index, IndexMut};

pub trait Arena<T> where T: std::fmt::Debug {
    fn remove(&mut self, idx: usize) -> Result<usize, String>;
    fn gc(&mut self) -> Result<Vec<ArenaItem<T>>, String>;
}

#[derive(Debug, Clone)]
pub enum ArenaItem<T> where T: std::fmt::Debug {
    // This is for storing actual data.
    Data(T),
    // This is for marking transported data's new index in the new arena.
    NewIndex(usize),
    // This is for slot whose former data has been permanently destroyed.
    None,
}

impl<T> ArenaItem<T> where T: std::fmt::Debug {
    pub fn replace(&mut self, new_index: usize) -> Self {
        std::mem::replace(self, ArenaItem::NewIndex(new_index))
    }
}

#[derive(Debug, Clone)]
pub struct IndexedArena<T> where T: std::fmt::Debug {
    pub entry: Option<usize>,
    pub map: HashMap<String, usize>,
    pub storage: Vec<ArenaItem<T>>,
}

impl<T> IndexedArena<T> where T: std::fmt::Debug {
    pub fn new() -> Self {
        Self {
            entry: None,
            map: HashMap::new(),
            storage: vec![ArenaItem::None],
        }
    }

    pub fn alloc(&mut self, data: T) -> Result<usize, String> {
        let index = self.storage.len();
        // if it's the first element, set it as head.
        if index == 0 {
            self.entry = Some(index);
        }
        self.storage.push(ArenaItem::Data(data));
        Ok(index)
    }

    pub fn add_name(&mut self, name: String, idx: usize) -> Result<(), String> {
        if self.map.contains_key(&name) {
            return Err("IndexedArena add_name: name already exists".to_string());
        }
        self.map.insert(name, idx);
        Ok(())
    }

    pub fn set_entry(&mut self, idx: usize) -> Result<(), String> {
        self.entry = Some(idx);
        Ok(())
    }

    pub fn get_by_name(&self, name: String) -> Result<Option<&T>, String> {
        match self.map.get(&name) {
            Some(&idx) => self.get(idx),
            None => Ok(None),
        }
    }

    pub fn get_mut_by_name(&mut self, name: String) -> Result<Option<&mut T>, String> {
        match self.map.get(&name) {
            Some(&idx) => self.get_mut(idx),
            None => Ok(None),
        }
    }

    pub fn get(&self, idx: usize) -> Result<Option<&T>, String> {
        if idx >= self.storage.len() {
            return Err("IndexedArena insert: index out of bounds".to_string());
        }
        // match None: the arena is empty
        // match Some(AreanaItem::Data): the arena has data at idx
        // match Some(AreanaItem::NewIndex): the arena has transported data at idx, invalid!
        // match Some(AreanaItem::None): the arena has deleted data at idx, invalid!
        if matches!(
            self.storage.get(idx),
            Some(ArenaItem::None) | Some(ArenaItem::NewIndex(_))
        ) {
            return Err("IndexedArena get: index points to None or NewIndex".to_string());
        }
        match self.storage.get(idx) {
            Some(ArenaItem::Data(node)) => Ok(Some(node)),
            _ => Ok(None),
        }
    }

    pub fn get_mut(&mut self, idx: usize) -> Result<Option<&mut T>, String> {
        if idx >= self.storage.len() {
            return Err("IndexedArena insert: index out of bounds".to_string());
        }
        if matches!(
            self.storage.get(idx),
            Some(ArenaItem::None) | Some(ArenaItem::NewIndex(_))
        ) {
            return Err("IndexedArena get_mut: index points to None or NewIndex".to_string());
        }
        match self.storage.get_mut(idx) {
            Some(ArenaItem::Data(node)) => Ok(Some(node)),
            _ => Ok(None),
        }
    }
}

impl<T> Index<usize> for IndexedArena<T> where T: std::fmt::Debug {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap().unwrap()
    }
}

impl<T> IndexMut<usize> for IndexedArena<T> where T: std::fmt::Debug {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).unwrap().unwrap()
    }
}

impl<T> Index<String> for IndexedArena<T> where T: std::fmt::Debug {
    type Output = T;

    fn index(&self, index: String) -> &Self::Output {
        self.get_by_name(index).unwrap().unwrap()
    }
}

impl<T> IndexMut<String> for IndexedArena<T> where T: std::fmt::Debug {
    fn index_mut(&mut self, index: String) -> &mut Self::Output {
        self.get_mut_by_name(index).unwrap().unwrap()
    }
}
