pub struct Queue<T> {
    elements: Vec<T>,
}

impl<T> Default for Queue<T> {
    fn default() -> Self {
        Queue {
            elements: Vec::new(),
        }
    }
}

impl<T> Queue<T> {
    pub fn new() -> Self {
        Queue {
            elements: Vec::new(),
        }
    }

    pub fn push(&mut self, element: T) {
        self.elements.push(element);
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.elements.is_empty() {
            None
        } else {
            Some(self.elements.remove(0))
        }
    }

    pub fn peek(&self) -> Option<&T> {
        self.elements.first()
    }

    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    pub fn len(&self) -> usize {
        self.elements.len()
    }

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
