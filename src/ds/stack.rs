
// Contents:
// - Stack struct
// - Implementation of Stack
// - Tests for Stack

/// A Stack data structure.
///
/// A stack is a data structure that allows elements to be added and removed in a last-in-first-out (LIFO) order.
/// 
/// # Examples
/// 
/// ```
/// use std_only::Stack;
/// 
/// let mut stack = Stack::new(10);
/// stack.push(1);
/// stack.push(2);
/// stack.push(3);
/// assert_eq!(stack.peek(), Some(&3));
/// assert_eq!(stack.pop(), Some(3));
/// assert_eq!(stack.pop(), Some(2));
/// assert_eq!(stack.pop(), Some(1));
/// assert_eq!(stack.pop(), None);
/// ```
#[derive(Debug)]
pub struct Stack<T> {
    #[cfg(not(feature = "static"))]
    elements: Vec<T>,
}

impl<T: Clone> Default for Stack<T> {
    /// Creates a new empty Stack
    ///
    /// Examples
    ///
    /// ```
    /// use std_only::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::default();
    /// assert!(stack.is_empty());
    /// ```
    fn default() -> Self {
        Stack {
            elements: Vec::new(),
        }
    }
}

impl<T: Clone> Stack<T> {
    /// Creates a new Stack with the specified capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The capacity for the new Stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new(10);
    /// assert_eq!(stack.get_capacity(), 10);
    /// ```
    pub fn new(capacity: usize) -> Self {
        Stack {
            elements: Vec::with_capacity(capacity),
        }
    }

    /// Pushes an element onto the Stack.
    ///
    /// # Arguments
    ///
    /// * `element` - The element to push onto the Stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::Stack;
    ///
    /// let mut stack = Stack::new(10);
    /// stack.push(1);
    /// assert_eq!(stack.pop(), Some(1));
    /// ```
    pub fn push(&mut self, element: T) {
        self.elements.push(element);
    }

    /// Pops an element from the Stack.
    ///
    /// # Returns
    ///
    /// * `Option<T>` - The popped element, or None if the Stack is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::Stack;
    ///
    /// let mut stack = Stack::new(10);
    /// assert_eq!(stack.pop(), None);
    ///
    /// stack.push(1);
    /// assert_eq!(stack.pop(), Some(1));
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.elements.pop()
    }

    /// Peeks at the top element of the Stack.
    /// 
    /// # Returns
    /// 
    /// * `Option<&T>` - A reference to the top element of the Stack, or None if the Stack is empty.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std_only::Stack;
    /// 
    /// let mut stack = Stack::new(10);
    /// assert_eq!(stack.peek(), None);
    /// 
    /// stack.push(1);
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.elements.last()
    }

    /// Checks if the Stack is empty.
    /// 
    /// # Returns
    /// 
    /// * `bool` - True if the Stack is empty, otherwise false.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std_only::Stack;
    /// 
    /// let mut stack = Stack::new(10);
    /// assert!(stack.is_empty());
    /// 
    /// stack.push(1);
    /// assert!(!stack.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Gets the capacity of the Stack.
    ///
    /// # Returns
    /// 
    /// * `usize` - The capacity of the Stack.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std_only::Stack;
    /// 
    /// let mut stack: Stack<i32> = Stack::new(10);
    /// assert_eq!(stack.get_capacity(), 10);
    /// ```
    pub fn get_capacity(&self) -> usize {
        self.elements.capacity()
    }

    /// Gets the number of elements of the Stack.
    ///
    /// # Returns
    /// 
    /// * `usize` - The number of elements of the Stack.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std_only::Stack;
    /// 
    /// let mut stack = Stack::new(10);
    /// stack.push(1);
    /// stack.push(2);
    /// assert_eq!(stack.len(), 2);
    /// 
    /// stack.pop();
    /// assert_eq!(stack.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Creates a new Stack from an array.
    /// 
    /// # Arguments
    /// 
    /// * `array` - The array to create the Stack from.
    /// 
    /// # Returns
    /// 
    /// * `Stack<T>` - The new Stack.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std_only::Stack;
    /// 
    /// let stack = Stack::from_array(&[1, 2, 3]);
    /// assert_eq!(stack.len(), 3);
    /// assert_eq!(stack.peek(), Some(&3));
    /// ```
    pub fn from_array(array: &[T]) -> Self
    where
        T: Clone,
    {
        Stack {
            elements: array.to_vec(),
        }
    }

    /// Pushes multiple elements onto the Stack.
    /// 
    /// # Arguments
    /// 
    /// * `items` - The elements to push onto the Stack.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std_only::Stack;
    /// 
    /// let mut stack = Stack::default();
    /// stack.push_many(&[1, 2, 3]);
    /// assert_eq!(stack.len(), 3);
    /// assert_eq!(stack.peek(), Some(&3));
    /// ```
    pub fn push_many(&mut self, items: &[T])
    where
        T: Clone,
    {
        self.elements.extend_from_slice(items);
    }

    /// Pops multiple elements from the Stack.
    /// 
    /// # Arguments
    /// 
    /// * `count` - The number of elements to pop.
    /// 
    /// # Returns
    /// 
    /// * `Option<Vec<T>>` - The popped elements, or None if the Stack does not contain enough elements.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std_only::Stack;
    /// 
    /// let mut stack = Stack::from_array(&[1, 2, 3]);
    /// let popped = stack.pop_many(2);
    /// assert_eq!(popped, Some(vec![2, 3]));
    /// assert_eq!(stack.len(), 1);
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    pub fn pop_many(&mut self, count: usize) -> Option<Vec<T>> {
        if self.elements.len() >= count {
            let start = self.elements.len() - count;
            let result = self.elements[start..].to_vec();
            self.elements.truncate(start);
            Some(result)
        } else {
            None
        }
    }

    /// Converts the Stack into a Vec.
    /// 
    /// # Returns
    /// 
    /// * `Vec<T>` - The Vec containing the elements of the Stack.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std_only::Stack;
    /// 
    /// let mut stack = Stack::from_array(&[1, 2, 3]);
    /// let vec = stack.into_vec();
    /// assert_eq!(vec, vec![1, 2, 3]);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.elements
    }

    /// Converts the Stack into a boxed slice.
    ///
    /// # Returns
    ///
    /// * `Box<[T]>` - The boxed slice containing the elements of the Stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::Stack;
    ///
    /// let mut stack = Stack::from_array(&[1, 2, 3]);
    /// let boxed_slice = stack.into_boxed_slice();
    /// assert_eq!(boxed_slice, vec![1, 2, 3].into_boxed_slice());
    /// ```
    pub fn into_boxed_slice(self) -> Box<[T]> {
        self.elements.into_boxed_slice()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_stack_is_empty() {
        let stack: Stack<i32> = Stack::default();
        assert_eq!(stack.is_empty(), true);
    }

    #[test]
    fn test_push_to_stack() {
        let mut stack = Stack::default();
        stack.push(1);
        assert_eq!(stack.is_empty(), false);
        assert_eq!(stack.len(), 1);
        assert_eq!(stack.peek(), Some(&1));
    }

    #[test]
    fn test_pop_from_stack() {
        let mut stack = Stack::default();
        stack.push(1);
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.is_empty(), true);
    }

    #[test]
    fn test_peek_at_stack() {
        let mut stack = Stack::default();
        stack.push(1);
        assert_eq!(stack.peek(), Some(&1));
    }

    #[test]
    fn test_stack_length() {
        let mut stack = Stack::default();
        stack.push(1);
        stack.push(2);
        stack.push(3);
        assert_eq!(stack.len(), 3);
    }

    #[test]
    fn test_from_array() {
        let array = [1, 2, 3];
        let stack = Stack::from_array(&array);
        assert_eq!(stack.len(), 3);
        assert_eq!(stack.peek(), Some(&3));
    }

    #[test]
    fn test_push_many() {
        let mut stack = Stack::default();
        stack.push_many(&[1, 2, 3]);
        assert_eq!(stack.len(), 3);
        assert_eq!(stack.peek(), Some(&3));
    }

    #[test]
    fn test_pop_many() {
        let mut stack = Stack::from_array(&[1, 2, 3]);
        let popped = stack.pop_many(2);
        assert_eq!(popped, Some(vec![2, 3]));
        assert_eq!(stack.len(), 1);
        assert_eq!(stack.peek(), Some(&1));
    }
}
