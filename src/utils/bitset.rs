use std::fmt;
use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Index, IndexMut, Sub, SubAssign,
};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BitSet {
    bits: Vec<u64>,
}

impl BitSet {
    pub fn new() -> Self {
        Self { bits: Vec::new() }
    }

    pub fn with_capacity(nbits: usize) -> Self {
        let len = (nbits + 63) / 64;
        Self {
            bits: Vec::with_capacity(len),
        }
    }

    pub fn insert(&mut self, bit: usize) -> bool {
        let idx = bit / 64;
        let offset = bit % 64;
        if idx >= self.bits.len() {
            self.bits.resize(idx + 1, 0);
        }
        let mask = 1 << offset;
        let present = (self.bits[idx] & mask) != 0;
        self.bits[idx] |= mask;
        !present
    }

    pub fn remove(&mut self, bit: usize) -> bool {
        let idx = bit / 64;
        if idx >= self.bits.len() {
            return false;
        }
        let offset = bit % 64;
        let mask = 1 << offset;
        let present = (self.bits[idx] & mask) != 0;
        self.bits[idx] &= !mask;
        present
    }

    pub fn contains(&self, bit: usize) -> bool {
        let idx = bit / 64;
        if idx >= self.bits.len() {
            return false;
        }
        let offset = bit % 64;
        (self.bits[idx] & (1 << offset)) != 0
    }

    pub fn clear(&mut self) {
        self.bits.clear();
    }

    pub fn len(&self) -> usize {
        self.bits.iter().map(|&w| w.count_ones() as usize).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.bits.iter().all(|&w| w == 0)
    }

    pub fn capacity(&self) -> usize {
        self.bits.len() * 64
    }

    pub fn num_words(&self) -> usize {
        self.bits.len()
    }
}

impl Index<usize> for BitSet {
    type Output = u64;

    fn index(&self, index: usize) -> &Self::Output {
        &self.bits[index]
    }
}

impl IndexMut<usize> for BitSet {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index >= self.bits.len() {
            self.bits.resize(index + 1, 0);
        }
        &mut self.bits[index]
    }
}

// Metaprogramming: Macro to implement binary operators
macro_rules! impl_bitop {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident, $op:tt) => {
        impl $trait for &BitSet {
            type Output = BitSet;

            fn $method(self, rhs: Self) -> Self::Output {
                let len = std::cmp::max(self.bits.len(), rhs.bits.len());
                let mut new_bits = Vec::with_capacity(len);
                for i in 0..len {
                    let lhs_word = self.bits.get(i).copied().unwrap_or(0);
                    let rhs_word = rhs.bits.get(i).copied().unwrap_or(0);
                    new_bits.push(lhs_word $op rhs_word);
                }
                // Trim trailing zeros? Optional, but good for equality checks
                while new_bits.last() == Some(&0) {
                    new_bits.pop();
                }
                BitSet { bits: new_bits }
            }
        }

        impl $assign_trait for BitSet {
            fn $assign_method(&mut self, rhs: Self) {
                let len = std::cmp::max(self.bits.len(), rhs.bits.len());
                if self.bits.len() < len {
                    self.bits.resize(len, 0);
                }
                for i in 0..len {
                    let rhs_word = rhs.bits.get(i).copied().unwrap_or(0);
                    self.bits[i] = self.bits[i] $op rhs_word;
                }
                while self.bits.last() == Some(&0) {
                    self.bits.pop();
                }
            }
        }

        impl $assign_trait<&BitSet> for BitSet {
            fn $assign_method(&mut self, rhs: &BitSet) {
                let len = std::cmp::max(self.bits.len(), rhs.bits.len());
                if self.bits.len() < len {
                    self.bits.resize(len, 0);
                }
                for i in 0..len {
                    let rhs_word = rhs.bits.get(i).copied().unwrap_or(0);
                    self.bits[i] = self.bits[i] $op rhs_word;
                }
                while self.bits.last() == Some(&0) {
                    self.bits.pop();
                }
            }
        }
    };
}

impl_bitop!(BitAnd, bitand, BitAndAssign, bitand_assign, &);
impl_bitop!(BitOr, bitor, BitOrAssign, bitor_assign, |);
impl_bitop!(BitXor, bitxor, BitXorAssign, bitxor_assign, ^);

// Difference is slightly different (lhs & !rhs), so we impl manually or make macro more generic.
// But set difference usually means remove items in rhs from lhs.
impl Sub for &BitSet {
    type Output = BitSet;

    fn sub(self, rhs: Self) -> Self::Output {
        let len = self.bits.len();
        let mut new_bits = Vec::with_capacity(len);
        for i in 0..len {
            let lhs_word = self.bits[i];
            let rhs_word = rhs.bits.get(i).copied().unwrap_or(0);
            new_bits.push(lhs_word & !rhs_word);
        }
        while new_bits.last() == Some(&0) {
            new_bits.pop();
        }
        BitSet { bits: new_bits }
    }
}

impl SubAssign for BitSet {
    fn sub_assign(&mut self, rhs: Self) {
        for i in 0..self.bits.len() {
            let rhs_word = rhs.bits.get(i).copied().unwrap_or(0);
            self.bits[i] &= !rhs_word;
        }
        while self.bits.last() == Some(&0) {
            self.bits.pop();
        }
    }
}

impl SubAssign<&BitSet> for BitSet {
    fn sub_assign(&mut self, rhs: &BitSet) {
        for i in 0..self.bits.len() {
            let rhs_word = rhs.bits.get(i).copied().unwrap_or(0);
            self.bits[i] &= !rhs_word;
        }
        while self.bits.last() == Some(&0) {
            self.bits.pop();
        }
    }
}

impl fmt::Debug for BitSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

// Iterator support
pub struct Iter<'a> {
    bitset: &'a BitSet,
    idx: usize,
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx / 64 < self.bitset.bits.len() {
            let word_idx = self.idx / 64;
            let bit_idx = self.idx % 64;
            let word = self.bitset.bits[word_idx];

            // Optimization: skip empty words
            if word == 0 {
                self.idx = (word_idx + 1) * 64;
                continue;
            }

            // Check bits in current word
            if (word & (1 << bit_idx)) != 0 {
                let ret = self.idx;
                self.idx += 1;
                return Some(ret);
            }

            // Find next set bit efficiently
            // Mask out bits before current bit_idx
            let masked_word = word & (!0 << bit_idx);
            if masked_word != 0 {
                let next_bit = masked_word.trailing_zeros() as usize;
                self.idx = word_idx * 64 + next_bit + 1;
                return Some(word_idx * 64 + next_bit);
            } else {
                self.idx = (word_idx + 1) * 64;
            }
        }
        None
    }
}

impl BitSet {
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            bitset: self,
            idx: 0,
        }
    }
}

// Metaprogramming: Initialization macro
#[macro_export]
macro_rules! bitset {
    () => {
        $crate::utils::bitset::BitSet::new()
    };
    ($($x:expr),+ $(,)?) => {
        {
            let mut bs = $crate::utils::bitset::BitSet::new();
            $(
                bs.insert($x);
            )+
            bs
        }
    };
}
