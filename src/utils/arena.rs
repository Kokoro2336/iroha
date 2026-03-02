/**
 * Simple arena allocator for indexed storage of values.
 * Faster retrieval by index compared to HashMap.
 */
use std::collections::HashMap;
use std::ops::{Index, IndexMut};

pub trait Arena<T>
where
    T: std::fmt::Debug,
{
    fn remove(&mut self, idx: usize) -> T;
    fn gc(&mut self) -> Vec<ArenaItem<T>>;
}

#[derive(Debug, Clone)]
pub enum ArenaItem<T>
where
    T: std::fmt::Debug,
{
    // This is for storing actual data.
    Data(T),
    // This is for marking transported data's new index in the new arena.
    NewIndex(usize),
    // This is for slot whose former data has been permanently destroyed.
    None,
}

impl<T> ArenaItem<T>
where
    T: std::fmt::Debug,
{
    pub fn replace(&mut self, new_index: usize) -> Self {
        std::mem::replace(self, ArenaItem::NewIndex(new_index))
    }
}

#[derive(Debug, Clone)]
pub struct IndexedArena<T>
where
    T: std::fmt::Debug,
{
    pub entry: Option<usize>,
    pub map: HashMap<String, usize>,
    pub storage: Vec<ArenaItem<T>>,
}

impl<T> IndexedArena<T>
where
    T: std::fmt::Debug,
{
    pub fn new() -> Self {
        Self {
            entry: None,
            map: HashMap::new(),
            storage: vec![],
        }
    }

    pub fn alloc(&mut self, data: T) -> usize {
        let index = self.storage.len();
        // if it's the first element, set it as head.
        if self.entry.is_none() {
            self.entry = Some(index);
        }
        self.storage.push(ArenaItem::Data(data));
        index
    }

    pub fn add_name(&mut self, name: String, idx: usize) {
        if self.map.contains_key(&name) {
            panic!("IndexedArena add_name: name already exists");
        }
        self.map.insert(name, idx);
    }

    pub fn set_entry(&mut self, idx: usize) {
        if idx >= self.storage.len() {
            panic!(
                "IndexedArena set_entry: index {} out of bounds, len: {}",
                idx,
                self.storage.len()
            );
        }
        self.entry = Some(idx);
    }

    pub fn get_by_name(&self, name: String) -> Option<&T> {
        match self.map.get(&name) {
            Some(&idx) => self.get(idx),
            None => None,
        }
    }

    pub fn get_mut_by_name(&mut self, name: String) -> Option<&mut T> {
        match self.map.get(&name) {
            Some(&idx) => self.get_mut(idx),
            None => None,
        }
    }

    pub fn get(&self, idx: usize) -> Option<&T> {
        if idx >= self.storage.len() {
            panic!(
                "IndexedArena get: index {} out of bounds, len: {}",
                idx,
                self.storage.len()
            );
        }
        match &self.storage[idx] {
            ArenaItem::Data(node) => Some(node),
            ArenaItem::None | ArenaItem::NewIndex(_) => {
                panic!("IndexedArena get: index {} points to None or NewIndex", idx);
            }
        }
    }

    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        if idx >= self.storage.len() {
            panic!(
                "IndexedArena get_mut: index {} out of bounds, len: {}",
                idx,
                self.storage.len()
            );
        }
        match &mut self.storage[idx] {
            ArenaItem::Data(node) => Some(node),
            ArenaItem::None | ArenaItem::NewIndex(_) => {
                panic!(
                    "IndexedArena get_mut: index {} points to None or NewIndex",
                    idx
                );
            }
        }
    }

    // Collect all the slots with data in the arena and return them as a vector.
    pub fn collect(&self) -> Vec<usize> {
        self.storage
            .iter()
            .enumerate()
            .filter_map(|(idx, item)| match item {
                ArenaItem::Data(_) => Some(idx),
                _ => None,
            })
            .collect()
    }

    // Replace the data at idx with new_item.
    pub fn replace(&mut self, idx: usize, new_item: T) {
        if idx >= self.storage.len() {
            panic!("IndexedArena replace: index {} out of bounds", idx);
        }
        if matches!(
            self.storage.get(idx),
            Some(ArenaItem::None) | Some(ArenaItem::NewIndex(_))
        ) {
            panic!(
                "IndexedArena replace: index {} points to None or NewIndex",
                idx
            );
        }
        self.storage[idx] = ArenaItem::Data(new_item);
    }
}

impl<T> Index<usize> for IndexedArena<T>
where
    T: std::fmt::Debug,
{
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<T> IndexMut<usize> for IndexedArena<T>
where
    T: std::fmt::Debug,
{
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

impl<T> Index<String> for IndexedArena<T>
where
    T: std::fmt::Debug,
{
    type Output = T;

    fn index(&self, index: String) -> &Self::Output {
        self.get_by_name(index).unwrap()
    }
}

impl<T> IndexMut<String> for IndexedArena<T>
where
    T: std::fmt::Debug,
{
    fn index_mut(&mut self, index: String) -> &mut Self::Output {
        self.get_mut_by_name(index).unwrap()
    }
}
