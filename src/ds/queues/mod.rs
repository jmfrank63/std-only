pub mod simple_queue;
pub mod priority_queue;

pub use priority_queue::PriorityQueue;
pub use simple_queue::SimpleQueue;

/// A trait for a queue data structure.
///
/// A queue is a data structure that allows elements to be inserted at the back
/// and removed from the front. This trait is similar to the standard library's
/// `std::collections::VecDeque` type, but it is more general and can be
/// implemented for a variety of data structures.
/// Give an example of a custom collection that implements Ord and for which
/// the Queue trait can be implemented.
/// 
/// # Examples
/// 
/// ```
/// use studylib::ds::queues::Queue;
/// 
/// struct MyQueue<T> {
///     data: Vec<T>,
/// }
/// 
/// impl<T: Ord> Queue<T> for MyQueue<T> {
///     fn is_empty(&self) -> bool {
///         self.data.is_empty()
///     }
/// 
///     fn len(&self) -> usize {
///         self.data.len()
///     }
/// 
///     fn push(&mut self, element: T) {
///         self.data.push(element);
///     }
/// 
///     fn pop(&mut self) -> Option<T> {
///         self.data.pop()
///     }
/// 
///     fn peek(&self) -> Option<&T> {
///         self.data.get(0)
///     }
/// }
/// 
/// let mut queue = MyQueue { data: Vec::new() };
/// 
/// assert_eq!(queue.is_empty(), true);
/// queue.push(1);
/// assert_eq!(queue.is_empty(), false);
/// assert_eq!(queue.peek(), Some(&1));
/// assert_eq!(queue.pop(), Some(1));
/// assert_eq!(queue.is_empty(), true);
/// assert_eq!(queue.pop(), None);
/// ```
pub trait Queue<T: Ord> {
    fn is_empty(&self) -> bool;
    fn len(&self) -> usize;
    fn push(&mut self, element: T);
    fn pop(&mut self) -> Option<T>;
    fn peek(&self) -> Option<&T>;
}
