// Contents:
// - PriorityQueue struct
// - Implementation of PriorityQueue
// - Tests for PriorityQueue

use crate::ds::heaps::{Heap, HeapType};

/// A priority queue data structure making use of a binary heap.
/// Use the heap we have already implemented to create a priority queue.
///
/// # Examples
///
/// ```
/// use studylib::ds::queues::PriorityQueue;
///
/// let mut pq = PriorityQueue::new();
/// pq.push(1, 1);
/// pq.push(2, 2);
/// pq.push(3, 3);
/// assert_eq!(pq.peek(), Some(&(3,3)));
/// assert_eq!(pq.pop(), Some((3, 3)));
/// assert_eq!(pq.pop(), Some((2, 2)));
/// assert_eq!(pq.pop(), Some((1, 1)));
/// assert_eq!(pq.pop(), None);
/// ```
#[derive(Debug)]
pub struct PriorityQueue<P, E> {
    heap: Heap<(P, E)>,
}

impl<P: Ord + Clone, E: Ord + Clone> PriorityQueue<P, E> {
    /// Creates a new empty PriorityQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::PriorityQueue;
    ///
    /// let mut pq: PriorityQueue<i32, i32> = PriorityQueue::new();
    /// assert!(pq.is_empty());
    /// ```
    pub fn new() -> Self {
        PriorityQueue {
            heap: Heap::new(HeapType::Max),
        }
    }

    /// Adds an element with a priority to the PriorityQueue.
    ///
    /// # Arguments
    ///
    /// * `element` - The element to add.
    /// * `priority` - The priority of the element.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::queues::PriorityQueue;
    ///
    /// let mut pq = PriorityQueue::new();
    /// pq.push(1, 1);
    /// pq.push(2, 2);
    /// pq.push(3, 3);
    /// assert_eq!(pq.len(), 3);
    /// ```
    pub fn push(&mut self, element: E, priority: P) {
        self.heap.push((priority, element));
    }

    /// Removes the element with the highest priority from the PriorityQueue and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::queues::PriorityQueue;
    ///
    /// let mut pq = PriorityQueue::new();
    /// pq.push(1, 1);
    /// pq.push(2, 2);
    /// pq.push(3, 3);
    /// assert_eq!(pq.pop(), Some((3, 3)));
    /// assert_eq!(pq.pop(), Some((2, 2)));
    /// assert_eq!(pq.pop(), Some((1, 1)));
    /// assert_eq!(pq.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<(P, E)> {
        self.heap.pop()
    }

    /// Returns a reference to the element with the highest priority.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::queues::PriorityQueue;
    ///
    /// let mut pq = PriorityQueue::new();
    /// pq.push(1, 1);
    /// pq.push(2, 2);
    /// pq.push(3, 3);
    /// assert_eq!(pq.peek(), Some(&(3, 3)));
    /// ```
    pub fn peek(&self) -> Option<&(P, E)> {
        self.heap.peek()
    }

    /// Returns the number of elements in the PriorityQueue.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::queues::PriorityQueue;
    ///
    /// let mut pq = PriorityQueue::new();
    /// assert_eq!(pq.len(), 0);
    /// pq.push(1, 1);
    /// pq.push(2, 2);
    /// pq.push(3, 3);
    /// assert_eq!(pq.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    /// Returns true if the PriorityQueue is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::queues::PriorityQueue;
    ///
    /// let mut pq = PriorityQueue::new();
    /// assert!(pq.is_empty());
    /// pq.push(1, 1);
    /// assert!(!pq.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    /// Creates a PriorityQueue from an array of tuples.
    ///
    /// # Arguments
    ///
    /// * `array` - A reference to an array of tuples.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::queues::PriorityQueue;
    ///
    /// let array = [(1, 1), (2, 2), (3, 3)];
    /// let pq = PriorityQueue::from_array(&array);
    /// assert_eq!(pq.len(), 3);
    /// assert_eq!(pq.peek(), Some(&(3, 3)));
    /// ```
    pub fn from_array(array: &[(P, E)]) -> Self {
        let mut pq = PriorityQueue::new();
        pq.push_many(array);
        pq
    }

    /// Adds many elements with their priorities to the PriorityQueue.
    ///
    /// # Arguments
    ///
    /// * `array` - A reference to an array of tuples.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::queues::PriorityQueue;
    ///
    /// let mut pq = PriorityQueue::new();
    /// pq.push_many(&[(1, 1), (2, 2), (3, 3)]);
    /// assert_eq!(pq.len(), 3);
    /// assert_eq!(pq.peek(), Some(&(3, 3)));
    /// ```
    pub fn push_many(&mut self, array: &[(P, E)]) {
        for (p, e) in array {
            self.push((*e).clone(), (*p).clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_priority_queue_is_empty() {
        let pq: PriorityQueue<i32, i32> = PriorityQueue::new();
        assert_eq!(pq.is_empty(), true);
    }

    #[test]
    fn test_push_to_priority_queue() {
        let mut pq = PriorityQueue::new();
        pq.push(1, 1);
        assert_eq!(pq.is_empty(), false);
        assert_eq!(pq.len(), 1);
        assert_eq!(pq.peek(), Some(&(1, 1)));
    }

    #[test]
    fn test_pop_from_priority_queue() {
        let mut pq = PriorityQueue::new();
        pq.push(1, 1);
        pq.push(2, 2);
        pq.push(3, 3);
        assert_eq!(pq.pop(), Some((3, 3)));
        assert_eq!(pq.pop(), Some((2, 2)));
        assert_eq!(pq.pop(), Some((1, 1)));
        assert_eq!(pq.pop(), None);
    }

    #[test]
    fn test_peek_at_priority_queue() {
        let mut pq = PriorityQueue::new();
        pq.push(1, 1);
        assert_eq!(pq.peek(), Some(&(1, 1)));
    }

    #[test]
    fn test_priority_queue_length() {
        let mut pq = PriorityQueue::new();
        pq.push(1, 1);
        pq.push(2, 2);
        pq.push(3, 3);
        assert_eq!(pq.len(), 3);
    }

    #[test]
    fn test_from_array() {
        let array = [(1, 1), (2, 2), (3, 3)];
        let mut pq = PriorityQueue::from_array(&array);
        assert_eq!(pq.len(), 3);
        assert_eq!(pq.pop(), Some((3, 3)));
    }

    #[test]
    fn test_push_many() {
        let mut pq = PriorityQueue::new();
        pq.push_many(&[(1, 1), (2, 2), (3, 3)]);
        assert_eq!(pq.len(), 3);
        assert_eq!(pq.pop(), Some((3, 3)));
    }
}
