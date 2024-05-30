// Contents:
// - Queue struct
// - Implementation of Queue
// - Tests for Queue

/// A Queue data structure.
///
/// A queue is a data structure that allows elements to be added and removed in a first-in-first-out (FIFO) order.
/// 
/// # Examples
/// 
/// ```
/// use std_only::Queue;
/// 
/// let mut queue = Queue::new();
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
pub struct Queue<T> {
    elements: Vec<T>,
}

/// Default implementation for Queue.
///
/// Creates a new empty Queue.
///
/// Examples
///
/// ```
/// use std_only::Queue;
///
/// let mut queue: Queue<i32> = Queue::default();
/// assert!(queue.is_empty());
/// ```
impl<T> Default for Queue<T> {
    fn default() -> Self {
        Queue {
            elements: Vec::new(),
        }
    }
}

impl<T> Queue<T> {
    /// Creates a new Queue.
    ///
    /// Examples
    ///
    /// ```
    /// use std_only::Queue;
    ///
    /// let mut queue: Queue<i32> = Queue::new();
    /// assert!(queue.is_empty());
    /// ```
    pub fn new() -> Self {
        Queue {
            elements: Vec::new(),
        }
    }

    /// Adds an element to the Queue.
    ///
    /// # Arguments
    ///
    /// * `element` - The element to add to the Queue.
    ///
    /// Examples
    ///
    /// ```
    /// use std_only::Queue;
    ///
    /// let mut queue = Queue::new();
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn push(&mut self, element: T) {
        self.elements.push(element);
    }

        /// Removes an element from the Queue.
    ///
    /// Returns the removed element, or None if the Queue is empty.
    ///
    /// Examples
    ///
    /// ```
    /// use std_only::Queue;
    ///
    /// let mut queue = Queue::new();
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

    /// Returns a reference to the first element in the Queue.
    ///
    /// Examples
    ///
    /// ```
    /// use std_only::Queue;
    ///
    /// let mut queue = Queue::new();
    /// queue.push(1);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.elements.first()
    }

    /// Checks if the Queue is empty.
    ///
    /// Examples
    ///
    /// ```
    /// use std_only::Queue;
    ///
    /// let mut queue = Queue::new();
    /// assert!(queue.is_empty());
    ///
    /// queue.push(1);
    /// assert!(!queue.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns the number of elements in the Queue.
    ///
    /// Examples
    ///
    /// ```
    /// use std_only::Queue;
    ///
    /// let mut queue = Queue::new();
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

    /// Creates a new Queue from an array.
    ///
    /// # Arguments
    ///
    /// * `array` - A slice of elements to create the Queue from.
    ///
    /// Examples
    ///
    /// ```
    /// use std_only::Queue;
    ///
    /// let queue = Queue::from_array(&[1, 2, 3]);
    /// assert_eq!(queue.is_empty(), false);
    /// assert_eq!(queue.len(), 3);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn from_array(array: &[T]) -> Self
    where
        T: Clone,
    {
        Queue {
            elements: array.to_vec(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_queue_new() {
        let queue: Queue<i32> = Queue::default();
        assert_eq!(queue.is_empty(), true);
        assert_eq!(queue.len(), 0);
    }

    #[test]
    fn test_queue_push() {
        let mut queue = Queue::default();
        queue.push(1);
        queue.push(2);
        queue.push(3);
        assert_eq!(queue.is_empty(), false);
        assert_eq!(queue.len(), 3);
    }

    #[test]
    fn test_queue_peek() {
        let mut queue = Queue::default();
        queue.push(1);
        assert_eq!(queue.peek(), Some(&1));
    }

    #[test]
    fn test_queue_pop() {
        let mut queue = Queue::default();
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
        let mut queue = Queue::default();
        queue.push(1);
        queue.pop();
        assert_eq!(queue.is_empty(), true);
        assert_eq!(queue.len(), 0);
    }

    #[test]
    fn test_queue_from_array_new() {
        let queue = Queue::from_array(&[1, 2, 3]);
        assert_eq!(queue.is_empty(), false);
        assert_eq!(queue.len(), 3);
    }

    #[test]
    fn test_queue_from_array_peek() {
        let queue = Queue::from_array(&[1, 2, 3]);
        assert_eq!(queue.peek(), Some(&1));
    }

    #[test]
    fn test_queue_from_array() {
        let queue = Queue::from_array(&[1, 2, 3]);
        assert_eq!(queue.is_empty(), false);
        assert_eq!(queue.len(), 3);
        assert_eq!(queue.peek(), Some(&1));
    }
}
