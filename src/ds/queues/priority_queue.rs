// Contents:
// - MaxPriorityQueue struct
// - Implementation of MaxPriorityQueue
// - Tests for MaxPriorityQueue

use crate::ds::heaps::BinaryMaxHeap;
use super::Queue;
use std::cmp::Ordering;

struct PriorityQueueItem<P, E>(P, E);

impl<P: Ord, E> PartialEq for PriorityQueueItem<P, E> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<P: Ord, E> Eq for PriorityQueueItem<P, E> {}

impl<P: Ord, E> PartialOrd for PriorityQueueItem<P, E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: Ord, E> Ord for PriorityQueueItem<P, E> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<P, E> From<(P, E)> for PriorityQueueItem<P, E> {
    fn from(item: (P, E)) -> Self {
        PriorityQueueItem(item.0, item.1)
    }
}

pub struct MaxPriorityQueue<P, E> {
    heap: BinaryMaxHeap<PriorityQueueItem<P, E>>,
}

impl<P: Ord, E> Default for MaxPriorityQueue<P, E> {
    fn default() -> Self {
        Self {
            heap: BinaryMaxHeap::default(),
        }
    }
}

impl<P: Ord + Default, E> Queue<E> for MaxPriorityQueue<P, E> {
    fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    fn len(&self) -> usize {
        self.heap.len()
    }

    fn push(&mut self, element: E) {
        self.heap.insert(PriorityQueueItem(P::default(), element));
    }

    fn pop(&mut self) -> Option<E> {
        self.heap.remove().map(|item| item.1)
    }

    fn peek(&self) -> Option<&E> {
        self.heap.peek().map(|item| &item.1)
    }

    fn clear(&mut self) {
        self.heap.clear();
    }
}

impl<P: Ord, E> MaxPriorityQueue<P, E> {
    /// Pushes an element with a priority to the MaxPriorityQueue.
    ///
    /// # Arguments
    ///
    /// * `priority` - The priority of the element to add to the MaxPriorityQueue.
    /// * `element` - The element to add to the MaxPriorityQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::MaxPriorityQueue;
    ///
    /// let mut queue = MaxPriorityQueue::default();
    /// queue.push(2, "b");
    /// queue.push(1, "a");
    /// queue.push(3, "c");
    /// assert_eq!(queue.peek(), Some((&3, &"c")));
    /// ```
    pub fn push(&mut self, priority: P, element: E) {
        self.heap.insert(PriorityQueueItem(priority, element));
    }

    /// Removes an element from the MaxPriorityQueue.
    ///
    /// Returns the removed element, or None if the MaxPriorityQueue is empty.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::MaxPriorityQueue;
    ///
    /// let mut queue = MaxPriorityQueue::default();
    /// queue.push(2, "b");
    /// queue.push(1, "a");
    /// queue.push(3, "c");
    /// assert_eq!(queue.pop(), Some((3, "c")));
    /// assert_eq!(queue.pop(), Some((2, "b")));
    /// assert_eq!(queue.pop(), Some((1, "a")));
    /// assert_eq!(queue.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<(P, E)> {
        self.heap.remove().map(|item| (item.0, item.1))
    }

    /// Returns the element with the highest priority without removing it from the MaxPriorityQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::MaxPriorityQueue;
    ///
    /// let mut queue = MaxPriorityQueue::default();
    /// queue.push(2, "b");
    /// queue.push(1, "a");
    /// queue.push(3, "c");
    /// assert_eq!(queue.peek(), Some((&3, &"c")));
    /// ```
    pub fn peek(&self) -> Option<(&P, &E)> {
        self.heap.peek().map(|item| (&item.0, &item.1))
    }

    /// Returns the number of elements in the MaxPriorityQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::MaxPriorityQueue;
    ///
    /// let mut queue = MaxPriorityQueue::default();
    /// queue.push(2, "b");
    /// queue.push(1, "a");
    /// queue.push(3, "c");
    /// assert_eq!(queue.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    /// Checks if the MaxPriorityQueue is empty.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::MaxPriorityQueue;
    ///
    /// let mut queue = MaxPriorityQueue::default();
    /// assert!(queue.is_empty());
    ///
    /// queue.push(1, "a");
    /// assert!(!queue.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    /// Clears the MaxPriorityQueue, removing all elements.
    /// 
    /// Examples
    /// 
    /// ```
    /// use studylib::ds::queues::MaxPriorityQueue;
    /// 
    /// let mut queue = MaxPriorityQueue::default();
    /// queue.push(1, "a");
    /// queue.push(2, "b");
    /// queue.clear();
    /// assert!(queue.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.heap.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_max_priority_queue_default() {
        let queue: MaxPriorityQueue<i32, i32> = MaxPriorityQueue::default();
        assert!(queue.is_empty());
    }

    #[test]
    fn test_max_priority_queue_push() {
        let mut queue = MaxPriorityQueue::default();

        queue.push(2, "b");

        assert!(!queue.is_empty());
        assert_eq!(queue.len(), 1);
    }

    #[test]
    fn test_max_priority_queue_pop() {
        let mut queue = MaxPriorityQueue::default();

        queue.push(2, "b");

        assert_eq!(queue.pop(), Some((2, "b")));
        assert_eq!(queue.pop(), None);
    }

    #[test]
    fn test_max_priority_queue_peek() {
        let mut queue = MaxPriorityQueue::default();

        queue.push(2, "b");

        assert_eq!(queue.peek(), Some((&2, &"b")));
        assert_eq!(queue.pop(), Some((2, "b")));
        assert_eq!(queue.peek(), None);
    }

    #[test]
    fn test_max_priority_queue_len() {
        let mut queue = MaxPriorityQueue::default();

        queue.push(2, "b");
        queue.push(3, "c");

        assert_eq!(queue.len(), 2);
        queue.pop();
        assert_eq!(queue.len(), 1);
    }

    #[test]
    fn test_max_priority_queue_is_empty() {
        let mut queue = MaxPriorityQueue::default();

        assert!(queue.is_empty());
        queue.push(1, "a");
        assert!(!queue.is_empty());
        queue.pop();
        assert!(queue.is_empty());
    }
    
    #[test]
    fn test_max_priority_queue_push_multiple() {
        let mut queue = MaxPriorityQueue::default();

        queue.push(2, "b");
        queue.push(1, "a");
        queue.push(3, "c");

        assert!(!queue.is_empty());
        assert_eq!(queue.len(), 3);
    }

    #[test]
    fn test_max_priority_queue_pop_multiple() {
        let mut queue = MaxPriorityQueue::default();

        queue.push(2, "b");
        queue.push(1, "a");
        queue.push(3, "c");

        assert_eq!(queue.pop(), Some((3, "c")));
        assert_eq!(queue.pop(), Some((2, "b")));
        assert_eq!(queue.pop(), Some((1, "a")));
        assert_eq!(queue.pop(), None);
    }

    #[test]
    fn test_max_priority_queue_peek_multiple() {
        let mut queue = MaxPriorityQueue::default();

        queue.push(2, "b");
        queue.push(1, "a");
        queue.push(3, "c");

        assert_eq!(queue.peek(), Some((&3, &"c")));
        assert_eq!(queue.pop(), Some((3, "c")));
        assert_eq!(queue.peek(), Some((&2, &"b")));
        assert_eq!(queue.pop(), Some((2, "b")));
        assert_eq!(queue.peek(), Some((&1, &"a")));
        assert_eq!(queue.pop(), Some((1, "a")));
        assert_eq!(queue.peek(), None);
    }

    #[test]
    fn test_max_priority_queue_len_multiple() {
        let mut queue = MaxPriorityQueue::default();

        queue.push(2, "b");
        queue.push(1, "a");
        queue.push(3, "c");

        assert_eq!(queue.len(), 3);
        queue.pop();
        assert_eq!(queue.len(), 2);
    }

    #[test]
    fn test_max_priority_queue_push_char() {
        let mut queue = MaxPriorityQueue::default();

        queue.push('b', 2);
        queue.push('a', 1);
        queue.push('c', 3);

        assert!(!queue.is_empty());
        assert_eq!(queue.len(), 3);
    }

    #[test]
    fn test_max_priority_queue_pop_char() {
        let mut queue = MaxPriorityQueue::default();

        queue.push('b', 2);
        queue.push('a', 1);
        queue.push('c', 3);

        assert_eq!(queue.pop(), Some(('c', 3)));
        assert_eq!(queue.pop(), Some(('b', 2)));
        assert_eq!(queue.pop(), Some(('a', 1)));
        assert_eq!(queue.pop(), None);
    }

    #[test]
    fn test_max_priority_queue_peek_char() {
        let mut queue = MaxPriorityQueue::default();

        queue.push('b', 2);
        queue.push('a', 1);
        queue.push('c', 3);

        assert_eq!(queue.peek(), Some((&'c', &3)));
        assert_eq!(queue.pop(), Some(('c', 3)));
        assert_eq!(queue.peek(), Some((&'b', &2)));
        assert_eq!(queue.pop(), Some(('b', 2)));
        assert_eq!(queue.peek(), Some((&'a', &1)));
        assert_eq!(queue.pop(), Some(('a', 1)));
        assert_eq!(queue.peek(), None);
    }

    #[test]
    fn test_max_priority_queue_len_char() {
        let mut queue = MaxPriorityQueue::default();

        queue.push('b', 2);
        queue.push('a', 1);
        queue.push('c', 3);

        assert_eq!(queue.len(), 3);
        queue.pop();
        assert_eq!(queue.len(), 2);
    }

    #[test]
    fn test_max_priority_queue_is_empty_char() {
        let mut queue = MaxPriorityQueue::default();

        assert!(queue.is_empty());
        queue.push('a', 1);
        assert!(!queue.is_empty());
        queue.pop();
        assert!(queue.is_empty());
    }
    
    // Add tests for string as a priority with float as element
    #[test]
    fn test_max_priority_queue_push_string_float() {
        let mut queue = MaxPriorityQueue::default();

        queue.push("b".to_string(), 2.0);
        queue.push("a".to_string(), 1.0);
        queue.push("c".to_string(), 3.0);

        assert!(!queue.is_empty());
        assert_eq!(queue.len(), 3);
    }

    #[test]
    fn test_max_priority_queue_pop_string_float() {
        let mut queue = MaxPriorityQueue::default();

        queue.push("b".to_string(), 2.0);
        queue.push("a".to_string(), 1.0);
        queue.push("c".to_string(), 3.0);

        assert_eq!(queue.pop(), Some(("c".to_string(), 3.0)));
        assert_eq!(queue.pop(), Some(("b".to_string(), 2.0)));
        assert_eq!(queue.pop(), Some(("a".to_string(), 1.0)));
        assert_eq!(queue.pop(), None);
    }

    #[test]
    fn test_max_priority_queue_peek_string_float() {
        let mut queue = MaxPriorityQueue::default();

        queue.push("b".to_string(), 2.0);
        queue.push("a".to_string(), 1.0);
        queue.push("c".to_string(), 3.0);

        assert_eq!(queue.peek(), Some((&"c".to_string(), &3.0)));
        assert_eq!(queue.pop(), Some(("c".to_string(), 3.0)));
        assert_eq!(queue.peek(), Some((&"b".to_string(), &2.0)));
        assert_eq!(queue.pop(), Some(("b".to_string(), 2.0)));
        assert_eq!(queue.peek(), Some((&"a".to_string(), &1.0)));
        assert_eq!(queue.pop(), Some(("a".to_string(), 1.0)));
        assert_eq!(queue.peek(), None);
    }

    #[test]
    fn test_max_priority_queue_len_string_float() {
        let mut queue = MaxPriorityQueue::default();

        queue.push("b".to_string(), 2.0);
        queue.push("a".to_string(), 1.0);
        queue.push("c".to_string(), 3.0);

        assert_eq!(queue.len(), 3);
        queue.pop();
        assert_eq!(queue.len(), 2);
    }

}
