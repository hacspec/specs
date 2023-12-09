pub trait FinMap: PartialEq + Clone {
    /// The type of keys in the map
    type K;
    /// The type of values in the map
    type V;

    /// Create a new empty map
    fn new() -> Self;
    /// Check if the map contains a key
    fn contains_key(&self, k: &Self::K) -> bool;
    /// Insert a key-value pair into the map
    fn insert(&self, k: Self::K, v: Self::V) -> Self;
    /// Get the value associated with a key
    fn get(&self, k: &Self::K) -> Option<&Self::V>;
    /// Remove a key-value pair from the map
    fn remove(&self, k: &Self::K) -> Self;
    /// Check if the map is empty
    fn is_empty(&self) -> bool;
    /// Get the number of key-value pairs in the map
    fn len(&self) -> usize;
    /// Get the keys in the map
    fn keys(&self) -> Vec<&Self::K>;
    /// Get the values in the map
    fn values(&self) -> Vec<&Self::V>;
}

pub mod vecmap;
pub use vecmap::FinMapVec;
