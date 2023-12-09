use crate::finmap::FinMap;
use hax_lib_macros as hax;
use std::vec::Vec;

/// A set implemented as a `Vec` with no duplicates
#[derive(Clone, PartialEq)]
pub struct FinMapVec<K, V>
where
    K: Copy + PartialEq + Ord,
    V: Copy + PartialEq,
{
    vec: Vec<(K, V)>,
}

impl<K, V> FinMap for FinMapVec<K, V>
where
    K: Copy + PartialEq + Ord,
    V: Copy + PartialEq,
{
    /// The type of keys in the map
    type K = K;
    /// The type of values in the map
    type V = V;

    /// Create a new empty map
    #[hax::ensures(|result|
        forall(|k : Self::K| !result.contains_key(k)) &&
        result.is_empty() &&
        forall(|k : Self::K| result.get(k) == None) &&
        forall(|k : Self::K| result.remove(k) == result) &&
        (result.len() == 0)
    )]
    fn new() -> Self {
        FinMapVec { vec: Vec::new() }
    }

    /// Check if the map contains a key
    #[hax::ensures(|result|
        (!result || !self.is_empty()) &&
        (result == (self.get(k) != None)) &&
        (result == (self.remove(k).len() == self.len() - 1)) &&
        forall(|v : Self::V| !result == (self.insert(k, v).remove(k) == self))
    )]
    fn contains_key(&self, k: &K) -> bool {
        self.vec.iter().any(|(k2, _)| k == k2)
    }

    /// Insert a key-value pair into the map
    #[hax::ensures(|result|
        result.contains_key(k) &&
        !result.is_empty() &&
        (result.get(k) == Some(v)) &&
        (result.remove(k).get(k) == None) &&
        (self.len() <= result.len() && result.len() <= self.len() + 1) &&
        forall(|v2 : Self::V| result.insert(k, v2) == self.insert(k, v2))
    )]
    fn insert(&self, k: K, v: V) -> Self {
        let mut new = self.clone();
        if new.is_empty() || !new.contains_key(&k) {
            new.vec.push((k, v));
        }
        new
    }

    /// Get the value associated with a key
    #[hax::ensures(|result|
        ((result == None) == !self.contains_key(k)) &&
        ((result != None) == !self.is_empty()) &&
        ((result != None) == (self.remove(k).len() == self.len() - 1)) &&
        ((result == None) == (self.remove(k).len() == self.len()))
    )]
    fn get(&self, k: &K) -> Option<&V> {
        self.vec.iter().find(|(k2, _)| k == k2).map(|(_, v)| v)
    }

    /// Remove a key-value pair from the map
    #[hax::ensures(|result|
        ((result.len() == self.len()) == !self.contains_key(k)) &&
        ((result.len() == self.len()) == (self.get(k) == None)) &&
        (self.len() - 1 <= result.len() && result.len() <= self.len()) &&
        (result.remove(k) == result) &&
        forall(|v : Self::V| result.insert(k, v) = self.insert(k, v))
    )]
    fn remove(&self, k: &K) -> Self {
        let mut new = self.clone();
        new.vec.retain(|(k2, _)| k != k2);
        new
    }

    /// Check if the map is empty
    #[hax::ensures(|result|
        forall(|k : Self::K| result == !result.contains_key(k)) &&
        forall(|k : Self::K| result == (self.get(k) == None)) &&
        forall(|k : Self::K| result == (self.remove(k) == self)) &&
        (result == (self.len() == 0))
    )]
    fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    /// Get the number of key-value pairs in the map
    #[hax::ensures(|result|
        (self.is_empty() == (result == 0)) &&
        (result >= 0)
    )]
    fn len(&self) -> usize {
        self.vec.len()
    }

    #[hax::ensures(|result|
        forall(|v: Self::V| result.contains(&v) == self.contains_key(&v))
    )]
    fn keys(&self) -> Vec<&Self::K> {
        self.into_iter().map(|(k, _)| k).collect()
    }

    #[hax::ensures(|result|
        forall(|k: Self::K| result.contains(&k) == self.get(&k).is_some())
    )]
    fn values(&self) -> Vec<&Self::V> {
        self.into_iter().map(|(_, v)| v).collect()
    }
}

impl<K, V> IntoIterator for FinMapVec<K, V>
where
    K: Copy + PartialEq + Ord,
    V: Copy + PartialEq,
{
    type Item = (K, V);
    type IntoIter = std::vec::IntoIter<Self::Item>;

    /// Create an iterator over the map
    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}

impl<'a, K, V> IntoIterator for &'a FinMapVec<K, V>
where
    K: Copy + PartialEq + Ord,
    V: Copy + PartialEq,
{
    type Item = &'a (K, V);
    type IntoIter = std::slice::Iter<'a, (K, V)>;

    /// Create an iterator over the map
    fn into_iter(self) -> Self::IntoIter {
        self.vec.iter()
    }
}

impl<K, V> FromIterator<(K, V)> for FinMapVec<K, V>
where
    K: Copy + PartialEq + Ord,
    V: Copy + PartialEq,
{
    /// Create a new map from an iterator
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut new = FinMapVec::new();
        new.vec = iter.into_iter().collect();
        new.vec.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
        new.vec.dedup_by(|(k1, _), (k2, _)| k1 == k2);
        new
    }
}
