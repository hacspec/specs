
// // use crate::prelude::*;
// use core::convert::TryFrom;
// use core::mem;
// use hacspec_lib::*;

// pub trait Hasher: Clone {
//     type Hash: Copy + PartialEq + Into<Vec<u8>> + TryFrom<Vec<u8>>;
//     fn hash(data: &[u8]) -> Self::Hash;
//     fn concat_and_hash(left: &Self::Hash, right: Option<&Self::Hash>) -> Self::Hash;
//     fn hash_size() -> usize;
// }

// //         let mut concatenated: Vec<u8> = (*left).into();

// //         match right {
// //             Some(right_node) => {
// //                 let mut right_node_clone: Vec<u8> = (*right_node).into();
// //                 concatenated.append(&mut right_node_clone);
// //                 Self::hash(&concatenated)
// //             }
// //             None => *left,
// //         }

// type PartialTreeLayer<H> = Vec<(usize, H)>;

// #[derive(Clone)]
// pub struct PartialTree<T: Hasher> {
//     layers: Vec<Vec<(usize, T::Hash)>>,
// }

// ///////////
// // Utils //
// ///////////
// pub fn is_left_index(index: usize) -> bool {
//     index % 2 == 0
// }

// pub fn get_sibling_index(index: usize) -> usize {
//     if is_left_index(index) {
//         // Right sibling index
//         index + 1
//     }
//     // Left sibling index
//     else {
//         index - 1
//     }
// }

// /// Rewritten tree_depth method to no longer make use of floats
// pub fn tree_depth(leaves_count: usize) -> usize {
//     let mut height = 0;
//     if leaves_count == 1 {
//         height = 1;
//     }
//     else {
//         height = usize::ilog2(leaves_count);
//     }
//     height as usize
//     // for i in 1..65usize {
//     //     if leaves_count <= usize::pow(2, i as u32) {
//     //         height = i;
//     //         return height;
//     //     }
//     // }
//     // height
// }

// pub fn parent_index(index: usize) -> usize {
//     if is_left_index(index) {
//         index / 2
//     }
//     else {
//         get_sibling_index(index) / 2
//     }
// }

// pub fn parent_indices(indices: &[usize]) -> Vec<usize> {
//     let mut parents: Vec<usize> = indices.iter().cloned().map(parent_index).collect();
//     parents.dedup();
//     parents
// }

// ///////////
// // Error //
// ///////////
// #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
// #[non_exhaustive]
// pub enum ErrorKind {
//     /// Serialized to bytes merkle proof can't be parsed because it can not be divided
//     SerializedProofSizeIsIncorrect,
//     /// Not enough helper nodes to calculate the root was passed to the [`PartialTree`].
//     ///
//     /// [`PartialTree`]: crate::PartialTree
//     NotEnoughHelperNodes,
//     HashConversionError,
//     NotEnoughHashesToCalculateRoot,
//     LeavesIndicesCountMismatch,
// }

// #[derive(Clone, Debug)]
// pub struct Error {
//     kind: ErrorKind,
// }

// impl Error {
//     pub fn new(kind: ErrorKind) -> Self {
//         Self { kind }
//     }

//     pub fn not_enough_helper_nodes() -> Self {
//         Self::new(
//             ErrorKind::NotEnoughHelperNodes
//         )
//     }
// }

// impl<T: Hasher> PartialTree<T> {
//     /// Takes leaves (item hashes) as an argument and build a Merkle Tree from them.
//     /// Since it's a partial tree, hashes must be accompanied by their index in the original tree.
//     pub fn new() -> Self {
//         Self { layers: Vec::new() }
//     }

//     /// This is a general algorithm for building a partial tree. It can be used to extract root
//     /// from merkle proof, or if a complete set of leaves provided as a first argument and no
//     /// helper indices given, will construct the whole tree.
//     fn build_tree(
//         mut partial_layers: Vec<Vec<(usize, T::Hash)>>,
//         full_tree_depth: usize,
//     ) -> Result<Vec<PartialTreeLayer<T::Hash>>, Error> {
//         let mut partial_tree: Vec<Vec<(usize, T::Hash)>> = Vec::new();
//         let mut current_layer = Vec::new();

//         // Reversing helper nodes, so we can remove one layer starting from 0 each iteration
//         let mut reversed_layers: Vec<Vec<(usize, T::Hash)>> =
//             partial_layers.drain(..).rev().collect();

//         // This iterates to full_tree_depth and not to the partial_layers_len because
//         // when constructing

//         // It is iterating to full_tree_depth instead of partial_layers.len to address the case
//         // of applying changes to a tree when tree requires a resize, and partial layer len
//         // in that case going to be lower that the resulting tree depth
//         for _ in 0..full_tree_depth {
//             // Appending helper nodes to the current known nodes
//             if let Some(mut nodes) = reversed_layers.pop() {
//                 current_layer.append(&mut nodes);
//             }
//             // current_layer.into_iter().is_sorted_by(|(a, _), (b, _)| a.cmp(b))
//             // current_layer.sort_by(|(a, _), (b, _)| a.cmp(b));
//             // TODO: SORT current_layer without using mutation!

//             // Adding partial layer to the tree
//             partial_tree.push(current_layer.clone());

//             // This empties `current` layer and prepares it to be reused for the next iteration
//             let (indices, nodes): (Vec<usize>, Vec<T::Hash>) = current_layer.drain(..).unzip();
//             let parent_layer_indices = parent_indices(&indices);

//             for (i, parent_node_index) in parent_layer_indices.iter().enumerate() {
//                 match nodes.get(i * 2) {
//                     // Populate `current_layer` back for the next iteration
//                     Some(left_node) => current_layer.push((
//                         *parent_node_index,
//                         T::concat_and_hash(left_node, nodes.get(i * 2 + 1)),
//                     )),
//                     None => return Err(Error::not_enough_helper_nodes()),
//                 }
//             }
//         }

//         partial_tree.push(current_layer.clone());

//         Ok(partial_tree)
//     }

//     pub fn build(partial_layers: Vec<Vec<(usize, T::Hash)>>, depth: usize) -> Result<Self, Error> {
//         let layers = Self::build_tree(partial_layers, depth)?;
//         Ok(Self { layers })
//     }

//     /// This is a helper function to build a full tree from a full set of leaves without any
//     /// helper indices
//     pub fn from_leaves(leaves: &[T::Hash]) -> Result<Self, Error> {
//         let leaf_tuples: Vec<(usize, T::Hash)> = leaves.iter().cloned().enumerate().collect();

//         Self::build(vec![leaf_tuples], tree_depth(leaves.len()))
//     }

//     /// Returns how many layers there is between leaves and the root
//     pub fn depth(&self) -> usize {
//         self.layers.len() - 1
//     }

//     // /// Return the root of the tree
//     // pub fn root(&self) -> Option<&T::Hash> {
//     //     Some(&self.layers.last()?.first()?.1)
//     // }

//     pub fn contains(&self, layer_index: usize, node_index: usize) -> bool {
//         match self.layers().get(layer_index) {
//             Some(layer) =>
//             {let mut temp = layer.clone().into_iter();
//              temp.any(|(index, _)| index == node_index)}
//             None => false,
//         }
//     }

//     // /// Consumes other partial tree into itself, replacing any conflicting nodes with nodes from
//     // /// `other` in the process. Doesn't rehash the nodes, so the integrity of the result is
//     // /// not verified. It gives an advantage in speed, but should be used only if the integrity of
//     // /// the tree can't be broken, for example, it is used in the `.commit` method of the
//     // /// `MerkleTree`, since both partial trees are essentially constructed in place and there's
//     // /// no need to verify integrity of the result.
//     // pub fn merge_unverified(mut self, other: Self) {
//     //     // Figure out new tree depth after merge
//     //     let depth_difference = other.layers().len() - self.layers().len();
//     //     let combined_tree_size = if depth_difference > 0 {
//     //         other.layers().len()
//     //     } else {
//     //         self.layers().len()
//     //     };

//     //     for layer_index in 0..combined_tree_size {
//     //         let mut combined_layer: Vec<(usize, T::Hash)> = Vec::new();

//     //         if let Some(self_layer) = self.layers().get(layer_index) {
//     //             let mut filtered_layer: Vec<(usize, T::Hash)> = self_layer
//     //                 .iter()
//     //                 .filter(|(node_index, _)| !other.contains(layer_index, *node_index))
//     //                 .cloned()
//     //                 .collect();

//     //             combined_layer.append(&mut filtered_layer);
//     //         }

//     //         if let Some(other_layer) = other.layers().get(layer_index) {
//     //             let mut cloned_other_layer = other_layer.clone();
//     //             combined_layer.append(&mut cloned_other_layer);
//     //         }

//     //         // combined_layer.sort_by(|(a, _), (b, _)| a.cmp(b));
//     //         // TODO: SORT combined_layer without using mutation!
//     //         self.upsert_layer(layer_index, combined_layer);
//     //     }
//     // }

//     /// Replace layer at a given index with a new layer. Used during tree merge
//     fn upsert_layer(// &
//                     mut self, layer_index: usize, mut new_layer: Vec<(usize, T::Hash)>) {
//         match self.layers.get(layer_index) {
//             Some(layer) => {
//                 // layer.clear();
//                 // layer.append(new_layer.as_mut())
//                 // TODO: Update layer without mutation!
//             }
//             None => { // self.layers.push(new_layer)
//             }
//         }
//     }

//     pub fn layer_nodes(&self) -> Vec<Vec<T::Hash>> {
//         let hashes: Vec<Vec<T::Hash>> = self
//             .layers()
//             .iter()
//             .map(|layer| layer.iter().cloned().map(|(_, hash)| hash).collect())
//             .collect();

//         hashes
//     }

//     /// Returns partial tree layers
//     pub fn layers(&self) -> &[Vec<(usize, T::Hash)>] {
//         &self.layers
//     }

//     /// Clears all elements in the ree
//     pub fn clear(// &
//                  mut self) {
//         // self.layers.clear();
//         // TODO: update layer without reference mutation
//     }
// }
