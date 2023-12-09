use crate::finset::FinSet;
use hax_lib_macros as hax;
use std::vec::Vec;

/// A set implemented as a `Vec` with no duplicates
#[derive(Clone, PartialEq)]
pub struct FinSetVec<V>
where
    V: Clone + PartialEq + Ord,
{
    vec: Vec<V>,
}

impl<V> FinSet for FinSetVec<V>
where
    V: Copy + PartialEq + Ord,
{
    /// The type of values in the set
    type V = V;

    /// Create a new empty set
    #[hax::ensures(|result|
        forall(|v : Self::V| !result.contains(&v) &&
        result.is_empty() &&
        forall(|v : Self::V| result.remove(&v) == result) &&
        (result.len() == 0))
    )]
    fn new() -> Self {
        FinSetVec { vec: Vec::new() }
    }

    /// Check if the set contains a value
    #[hax::ensures(|result|
        (result == !self.is_empty()) &&
        (result == (self.remove(v).len() == self.len() - 1))
    )]
    fn contains(&self, v: &V) -> bool {
        self.vec.contains(v)
    }

    /// Insert a value into the set
    #[hax::ensures(|result|
        result.contains(v) &&
        !result.is_empty() &&
        (!self.contains(v) == (result.remove(v) == self)) &&
        (self.len() <= result.len() && result.len() <= self.len() + 1) &&
        (result.remove(v) == self) &&
        (result.insert(v) == result)
    )]
    fn insert(&self, v: V) -> Self {
        let mut new = self.clone();
        if new.is_empty() || !new.contains(&v) {
            new.vec.push(v);
        }
        new
    }

    /// Remove a value from the set
    #[hax::ensures(|result|
        ((result.len() == self.len()) == !self.contains(v)) &&
        (self.len() - 1 <= result.len() && result.len() <= self.len()) &&
        (result.insert(v) == self) &&
        (result.remove(v) == result)
    )]
    fn remove(&self, v: &Self::V) -> Self {
        let mut new = self.clone();
        new.vec.retain(|x| x != v);
        new
    }

    /// Check if the set is empty
    #[hax::ensures(|result|
        forall(|v : Self::V| result == !self.contains(&v)) &&
        forall(|v : Self::V| result == (self.remove(v) == self)) &&
        (result == (self.len() == 0))
    )]
    fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    /// Get the number of values in the set
    #[hax::ensures(|result|
        (self.is_empty() == (result == 0)) &&
        result >= 0
    )]
    fn len(&self) -> usize {
        self.vec.len()
    }

    /// Create a union with another set
    #[hax::ensures(|result|
        forall(|v : Self::V| self.contains(&v) && other.contains(&v) == result.contains(&v)) &&
        (other != self || result == self) &&
        (result == other.union(self)) &&
        forall(|s : Self| self.union(other.union(s)) == (self.union(other)).union(s))
    )]
    fn union(&self, other: &Self) -> Self {
        let mut new = self.clone();
        new.vec.extend(other.vec.iter().cloned());
        new.vec.sort();
        new.vec.dedup();
        new
    }

    /// Create an intersection with another set
    #[hax::ensures(|result|
        forall(|v : Self::V| self.contains(&v) && other.contains(&v) == result.contains(&v)) &&
        (other != self || result == self) &&
        (result == other.intersection(self)) &&
        forall(|s : Self| self.intersection(other.intersection(s)) == (self.intersection(other)).intersection(s))
    )]
    fn intersection(&self, other: &Self) -> Self {
        let mut new = self.clone();
        new.vec.retain(|x| other.contains(x));
        new
    }

    /// Create a difference with another set
    #[hax::ensures(|result|
        forall(|v : Self::V| self.contains(&v) && !other.contains(&v) == result.contains(&v)) &&
        (other != self || result.is_empty())
    )]
    fn difference(&self, other: &Self) -> Self {
        let mut new = self.clone();
        let other = other.clone();
        new.vec.retain(|x| !other.contains(x));
        new
    }

    /// Create a symmetric difference with another set
    #[hax::ensures(|result|
        forall(|v : Self::V| (self.contains(&v) != other.contains(&v)) == result.contains(&v)) &&
        (other != self || result.is_empty()) &&
        (result == other.symmetric_difference(self)) &&
        forall(|s : Self| self.symmetric_difference(other.symmetric_difference(s)) == (self.symmetric_difference(other)).symmetric_difference(s)) &&
        (result == self.union(other).difference(self.intersection(other)))
    )]
    fn symmetric_difference(&self, other: &Self) -> Self {
        self.difference(other).union(&other.difference(self))
    }
}

impl<V> IntoIterator for FinSetVec<V>
where
    V: Clone + PartialEq + Ord,
{
    type Item = V;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    /// Create an iterator over a set
    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}

impl<'a, V> IntoIterator for &'a FinSetVec<V>
where
    V: Copy + PartialEq + Ord,
{
    type Item = &'a V;
    type IntoIter = std::slice::Iter<'a, V>;

    /// Create an iterator over a set
    fn into_iter(self) -> Self::IntoIter {
        self.vec.iter()
    }
}

impl<V> FromIterator<V> for FinSetVec<V>
where
    V: Copy + Clone + PartialEq + Ord,
{
    /// Create a set from an iterator
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        let mut new = FinSetVec::new();
        new.vec = iter.into_iter().collect();
        new.vec.sort();
        new.vec.dedup();
        new
    }
}
