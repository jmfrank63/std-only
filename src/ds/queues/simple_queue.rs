// Contents:
// - SimpleQueue struct
// - Implementation of SimpleQueue
// - Tests for SimpleQueue

use super::Queue;

/// A SimpleQueue data structure.
///
/// A queue is a data structure that allows elements to be added and removed in a first-in-first-out (FIFO) order.
///
/// # Examples
///
/// ```
/// use studylib::ds::queues::SimpleQueue;
///
/// let mut queue = SimpleQueue::default();
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
        Self {
            elements: Vec::new(),
        }
    }
}

impl<T> Queue<T> for SimpleQueue<T> {
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
    /// let mut queue = SimpleQueue::default();
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    fn push(&mut self, element: T) {
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
    /// let mut queue = SimpleQueue::default();
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.pop(), Some(1));
    /// assert_eq!(queue.pop(), Some(2));
    /// assert_eq!(queue.pop(), Some(3));
    /// assert_eq!(queue.pop(), None);
    /// ```
    fn pop(&mut self) -> Option<T> {
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
    /// let mut queue = SimpleQueue::default();
    /// queue.push(1);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    fn peek(&self) -> Option<&T> {
        self.elements.first()
    }

    /// Checks if the SimpleQueue is empty.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::default();
    /// assert!(queue.is_empty());
    ///
    /// queue.push(1);
    /// assert!(!queue.is_empty());
    /// ```
    fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns the number of elements in the SimpleQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::default();
    /// assert_eq!(queue.len(), 0);
    ///
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.len(), 3);
    /// ```
    fn len(&self) -> usize {
        self.elements.len()
    }

    /// Clears the SimpleQueue, removing all elements.
    /// 
    /// Examples
    /// 
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    /// 
    /// let mut queue = SimpleQueue::default();
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// queue.clear();
    /// assert_eq!(queue.is_empty(), true);
    /// ```
    fn clear(&mut self) {
        self.elements.clear();
    }
}

impl<T> SimpleQueue<T> {
    /// Pushes an element to the SimpleQueue.
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
    /// let mut queue = SimpleQueue::default();
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn push(&mut self, element: T) {
        Queue::push(self, element);
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
    /// let mut queue = SimpleQueue::default();
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.pop(), Some(1));
    /// assert_eq!(queue.pop(), Some(2));
    /// assert_eq!(queue.pop(), Some(3));
    /// assert_eq!(queue.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        Queue::pop(self)
    }

    /// Returns a reference to the first element in the SimpleQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::default();
    /// queue.push(1);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        Queue::peek(self)
    }

    /// Checks if the SimpleQueue is empty.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::default();
    /// assert!(queue.is_empty());
    ///
    /// queue.push(1);
    /// assert!(!queue.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        Queue::is_empty(self)
    }

    /// Returns the number of elements in the SimpleQueue.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    ///
    /// let mut queue = SimpleQueue::default();
    /// assert_eq!(queue.len(), 0);
    ///
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// assert_eq!(queue.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        Queue::len(self)
    }

    /// Clears the SimpleQueue, removing all elements.
    /// 
    /// Examples
    /// 
    /// ```
    /// use studylib::ds::queues::SimpleQueue;
    /// 
    /// let mut queue = SimpleQueue::default();
    /// queue.push(1);
    /// queue.push(2);
    /// queue.push(3);
    /// queue.clear();
    /// assert_eq!(queue.is_empty(), true);
    /// ```
    pub fn clear(&mut self) {
        Queue::clear(self);
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
}
