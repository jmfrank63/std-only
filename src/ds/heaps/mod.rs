pub mod binary_min_heap;
pub mod binary_max_heap;

pub use binary_min_heap::BinaryMinHeap;
pub use binary_max_heap::BinaryMaxHeap;

pub trait Heap<T: Ord> {
    fn insert(&mut self, item: T);
    fn remove(&mut self) -> Option<T>;
    fn peek(&self) -> Option<&T>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn merge(&mut self, other: Self);
}
