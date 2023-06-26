// #[derive(Copy, Clone)]
// pub struct BoundedIndex<const MAX: usize>(pub usize);

// use std::ops::{Index, IndexMut};

// impl<const MAX: usize, T> Index<BoundedIndex<MAX>> for [T; MAX] {
//     type Output = T;
//     fn index(&self, BoundedIndex(i): BoundedIndex<MAX>) -> &T {
//         self.index(i)
//     }
// }

// impl<const MAX: usize, T> IndexMut<BoundedIndex<MAX>> for [T; MAX] {
//     fn index_mut(&mut self, BoundedIndex(i): BoundedIndex<MAX>) -> &mut T {
//         self.index_mut(i)
//     }
// }
