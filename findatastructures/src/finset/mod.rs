pub trait FinSet: PartialEq + Clone {
    /// The type of values in the set
    type V;

    /// Create a new empty set
    fn new() -> Self;
    /// Check if the set contains a value
    fn contains(&self, v: &Self::V) -> bool;
    /// Insert a value into the set
    fn insert(&self, v: Self::V) -> Self;
    /// Remove a value from the set
    fn remove(&self, v: &Self::V) -> Self;
    /// Check if the set is empty
    fn is_empty(&self) -> bool;
    /// Get the number of values in the set
    fn len(&self) -> usize;

    /// Create a union with another set
    fn union(&self, other: &Self) -> Self;
    /// Create an intersection with another set
    fn intersection(&self, other: &Self) -> Self;
    /// Create a difference with another set
    fn difference(&self, other: &Self) -> Self;
    /// Create a symmetric difference with another set
    fn symmetric_difference(&self, other: &Self) -> Self;
}

pub mod vecset;
pub use vecset::FinSetVec;
