use hacspec_lib::*;

pub trait Hasher: Clone {
    type Hash: Copy + PartialEq + Into<Vec<u8>> + TryFrom<Vec<u8>>;
    fn hash(data: &[u8]) -> Self::Hash;
    fn concat_and_hash(left: &Self::Hash, right: Option<&Self::Hash>) -> Self::Hash;
    fn hash_size() -> usize ;
}
