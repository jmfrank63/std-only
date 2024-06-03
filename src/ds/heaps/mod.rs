pub mod binary_min_heap;
pub mod binary_max_heap;

pub use binary_min_heap::BinaryMinHeap;
pub use binary_max_heap::BinaryMaxHeap;

/// A trait for a heap data structure.
///
/// A heap is a binary tree data structure that satisfies the heap property.
/// This property states that the value of each node is less than or equal to
/// the values of its children. A heap can be implemented as a binary tree,
/// but it is usually stored in an array for efficiency.
/// Give an example of a custom collection that implements Ord and for which
/// the Heap trait can be implemented.
/// 
/// # Examples
/// 
/// ```
/// use studylib::ds::heaps::Heap;
/// 
/// struct MyHeap<T> {
///     data: Vec<T>,
/// }
/// 
/// impl<T: Ord> Heap<T> for MyHeap<T> {
///     fn insert(&mut self, item: T) {
///         self.data.push(item);
///         self.data.sort();
///     }
/// 
///     fn remove(&mut self) -> Option<T> {
///         self.data.pop()
///     }
/// 
///     fn peek(&self) -> Option<&T> {
///         self.data.last()
///     }
/// 
///     fn len(&self) -> usize {
///         self.data.len()
///     }
/// 
///     fn is_empty(&self) -> bool {
///         self.data.is_empty()
///     }
/// 
///     fn merge(&mut self, other: Self) {
///         self.data.extend(other.data);
///         self.data.sort();
///     }
/// 
///     fn clear(&mut self) {
///       self.data.clear();
///     }
/// }
/// 
/// let mut heap = MyHeap { data: Vec::new() };
/// 
/// assert_eq!(heap.is_empty(), true);
/// heap.insert(1);
/// assert_eq!(heap.is_empty(), false);
/// assert_eq!(heap.peek(), Some(&1));
/// assert_eq!(heap.remove(), Some(1));
/// assert_eq!(heap.is_empty(), true);
/// assert_eq!(heap.remove(), None);
/// ```
pub trait Heap<T: Ord> {
    fn insert(&mut self, item: T);
    fn remove(&mut self) -> Option<T>;
    fn peek(&self) -> Option<&T>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn merge(&mut self, other: Self);
    fn clear(&mut self);
}
