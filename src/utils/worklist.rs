/// Worklist implementation for IR optimization passes.
use crate::utils::bitset::BitSet;

use rustc_hash::FxHashSet;
use std::collections::VecDeque;
use std::hash::Hash;

pub struct Worklist<T, S> {
    list: VecDeque<T>,
    in_list: S,
}

pub trait WorklistTrait<T> {
    fn new() -> Self;
    fn push(&mut self, item: T);
    fn pop(&mut self) -> Option<T>;
    fn is_empty(&self) -> bool;
    fn len(&self) -> usize;
    fn clear(&mut self);
    fn contains(&self, item: &T) -> bool;
}

/// If the items can not be easily converted to usize and hashable, we use a hash set to track membership.
impl<T: Eq + Hash + Clone> WorklistTrait<T> for Worklist<T, FxHashSet<T>> {
    fn new() -> Self {
        Self {
            list: VecDeque::new(),
            in_list: FxHashSet::default(),
        }
    }

    fn push(&mut self, item: T) {
        if self.in_list.insert(item.clone()) {
            self.list.push_back(item);
        }
    }

    fn pop(&mut self) -> Option<T> {
        if let Some(item) = self.list.pop_front() {
            self.in_list.remove(&item);
            Some(item)
        } else {
            None
        }
    }

    fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    fn len(&self) -> usize {
        self.list.len()
    }

    fn clear(&mut self) {
        self.list.clear();
        self.in_list.clear();
    }

    fn contains(&self, item: &T) -> bool {
        self.in_list.contains(item)
    }
}

/// If the items can be easily converted to usize, we can use a bitset to track membership for better performance.
impl<T: Into<usize> + Copy> WorklistTrait<T> for Worklist<T, BitSet> {
    fn new() -> Self {
        Self {
            list: VecDeque::new(),
            in_list: BitSet::new(),
        }
    }

    fn push(&mut self, item: T) {
        let index = item.into();
        if !self.in_list.contains(index) {
            self.in_list.insert(index);
            self.list.push_back(item);
        }
    }

    fn pop(&mut self) -> Option<T> {
        if let Some(item) = self.list.pop_front() {
            let index = item.into();
            self.in_list.remove(index);
            Some(item)
        } else {
            None
        }
    }

    fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    fn len(&self) -> usize {
        self.list.len()
    }

    fn clear(&mut self) {
        self.list.clear();
        self.in_list.clear();
    }

    fn contains(&self, item: &T) -> bool {
        let index = (*item).into();
        self.in_list.contains(index)
    }
}
