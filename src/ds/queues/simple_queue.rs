// Contents:
// - SimpleQueue struct
// - Implementation of SimpleQueue
// - Tests for SimpleQueue

/// A SimpleQueue data structure.
///
/// A queue is a data structure that allows elements to be added and removed in a first-in-first-out (FIFO) order.
///
/// # Examples
///
/// ```
/// use studylib::ds::queues::SimpleQueue;
///
/// let mut queue = SimpleQueue::new();
/// queue.push(1);
/// queue.push(2);
/// queue.push(3);
/// assert_eq!(queue.peek(), Some(&1));
/// assert_eq!(queue.pop(), Some(1));
/// assert_eq!(queue.pop(), Some(2));
/// assert_eq!(queue.pop(), Some(3));
/// assert_eq!(queue.pop(), None);
/// ```
#[derive(Debug)]
pub struct SimpleQueue<T> {
    elements: Vec<T>,
}

impl<T> Default for SimpleQueue<T> {
    /// Default implementation for SimpleQueue.
    ///
    /// Creates a new empty SimpleQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue: SimpleQueue<i32> = SimpleQueue::default();
    /// assert!(queue.is_empty());
    /// ```
    fn default() -> Self {
        SimpleQueue {
            elements: Vec::new(),
        }
    }
}

impl<T> SimpleQueue<T> {
    /// Creates a new SimpleQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue: SimpleQueue<i32> = SimpleQueue::new();
    /// assert!(queue.is_empty());
    /// ```
    pub fn new() -> Self {
        SimpleQueue {
            elements: Vec::new(),
        }
    }

    /// Adds an element to the SimpleQueue.
    ///
    /// # Arguments
    ///
    /// * `element` - The element to add to the SimpleQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::new();
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn push(&mut self, element: T) {
        self.elements.push(element);
    }

    /// Removes an element from the SimpleQueue.
    ///
    /// Returns the removed element, or None if the SimpleQueue is empty.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::new();
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.pop(), Some(1));
    /// assert_eq!(queue.pop(), Some(2));
    /// assert_eq!(queue.pop(), Some(3));
    /// assert_eq!(queue.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.elements.is_empty() {
            None
        } else {
            Some(self.elements.remove(0))
        }
    }

    /// Returns a reference to the first element in the SimpleQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::new();
    /// queue.push(1);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.elements.first()
    }

    /// Checks if the SimpleQueue is empty.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::new();
    /// assert!(queue.is_empty());
    ///
    /// queue.push(1);
    /// assert!(!queue.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns the number of elements in the SimpleQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::new();
    /// assert_eq!(queue.len(), 0);
    ///
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Creates a new SimpleQueue from an array.
    ///
    /// # Arguments
    ///
    /// * `array` - A slice of elements to create the SimpleQueue from.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let queue = SimpleQueue::from_array(&[1, 2, 3]);
    /// assert_eq!(queue.is_empty(), false);
    /// assert_eq!(queue.len(), 3);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn from_array(array: &[T]) -> Self
    where
        T: Clone,
    {
        SimpleQueue {
            elements: array.to_vec(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_queue_default() {
        let queue: SimpleQueue<i32> = SimpleQueue::default();
        assert_eq!(queue.is_empty(), true);
        assert_eq!(queue.len(), 0);
    }

    #[test]
    fn test_queue_new() {
        let queue: SimpleQueue<i32> = SimpleQueue::new();
        assert_eq!(queue.is_empty(), true);
        assert_eq!(queue.len(), 0);
    }

    #[test]
    fn test_queue_push() {
        let mut queue = SimpleQueue::default();
        queue.push(1);
        queue.push(2);
        queue.push(3);
        assert_eq!(queue.is_empty(), false);
        assert_eq!(queue.len(), 3);
    }

    #[test]
    fn test_queue_peek() {
        let mut queue = SimpleQueue::default();
        queue.push(1);
        assert_eq!(queue.peek(), Some(&1));
    }

    #[test]
    fn test_queue_pop() {
        let mut queue = SimpleQueue::default();
        queue.push(1);
        queue.push(2);
        queue.push(3);
        assert_eq!(queue.pop(), Some(1));
        assert_eq!(queue.pop(), Some(2));
        assert_eq!(queue.pop(), Some(3));
        assert_eq!(queue.pop(), None);
    }

    #[test]
    fn test_queue_is_empty_after_pop() {
        let mut queue = SimpleQueue::default();
        queue.push(1);
        queue.pop();
        assert_eq!(queue.is_empty(), true);
        assert_eq!(queue.len(), 0);
    }

    #[test]
    fn test_queue_from_array_new() {
        let queue = SimpleQueue::from_array(&[1, 2, 3]);
        assert_eq!(queue.is_empty(), false);
        assert_eq!(queue.len(), 3);
    }

    #[test]
    fn test_queue_from_array_peek() {
        let queue = SimpleQueue::from_array(&[1, 2, 3]);
        assert_eq!(queue.peek(), Some(&1));
    }

    #[test]
    fn test_queue_from_array() {
        let queue = SimpleQueue::from_array(&[1, 2, 3]);
        assert_eq!(queue.is_empty(), false);
        assert_eq!(queue.len(), 3);
        assert_eq!(queue.peek(), Some(&1));
    }
}
