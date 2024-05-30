// Contents:
// - StaticStack struct
// - Implementation of StaticStack
// - Tests for StaticStack

/// A Stack data structure.
///
/// A stack is a data structure that allows elements to be added and removed in a last-in-first-out (LIFO) order.
/// 
/// # Examples
/// 
/// ```
/// use std_only::StaticStack;
/// 
/// let mut stack = StaticStack::new(10);
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
pub struct StaticStack<T> {
    elements: Box<[Option<T>]>,
    top: usize,
}

impl<T: Clone> Default for StaticStack<T> {
    /// Creates a new empty Stack
    ///
    /// Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack: StaticStack<i32> = StaticStack::default();
    /// assert!(stack.is_empty());
    /// ```
    fn default() -> Self {
        Self {
            elements: vec![None; 10].into_boxed_slice(),
            top: 0,
        }
    }
}

impl<T: Clone> StaticStack<T> {
    /// Creates a new Stack with the specified capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The capacity for the new Stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack = StaticStack::new(10);
    /// stack.push(1);
    /// stack.push(2);
    /// stack.push(3);
    /// assert_eq!(stack.peek(), Some(&3));
    /// ```
    pub fn new(size: usize) -> Self {
        Self {
            elements: vec![None; size].into_boxed_slice(),
            top: 0,
        }
    }

    /// Adds an element to the top of the stack.
    ///
    /// # Arguments
    ///
    /// * `element` - The element to add to the stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack = StaticStack::new(10);
    /// stack.push(1);
    /// 
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    pub fn push(&mut self, element: T) {
        if self.top < self.elements.len() {
            self.elements[self.top] = Some(element);
            self.top += 1;
        }
    }

    /// Removes and returns the element at the top of the stack.
    ///
    /// # Returns
    ///
    /// * `Some(T)` - The element at the top of the stack.
    /// * `None` - If the stack is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack = StaticStack::new(10);
    /// stack.push(1);
    /// 
    /// assert_eq!(stack.pop(), Some(1));
    /// assert_eq!(stack.is_empty(), true);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.top > 0 {
            self.top -= 1;
            self.elements[self.top].take()
        } else {
            None
        }
    }

    /// Returns a reference to the element at the top of the stack without removing it.
    ///
    /// # Returns
    ///
    /// * `Option<&T>` - A reference to the element at the top of the stack.
    /// * `None` - If the stack is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack = StaticStack::new(10);
    /// stack.push(1);
    /// 
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.elements.get(self.top - 1).and_then(|x| x.as_ref())
    }

    /// Checks if the stack is empty.
    ///
    /// # Returns
    ///
    /// * `true` - If the stack is empty.
    /// * `false` - If the stack is not empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack = StaticStack::new(10);
    /// assert_eq!(stack.is_empty(), true);
    /// 
    /// stack.push(1);
    /// assert_eq!(stack.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.top == 0
    }

    /// Returns the number of elements in the stack.
    ///
    /// # Returns
    ///
    /// * `usize` - The number of elements in the stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack = StaticStack::new(10);
    /// stack.push(1);
    /// stack.push(2);
    /// stack.push(3);
    /// assert_eq!(stack.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.top
    }

    /// Returns the capacity of the stack.
    ///
    /// # Returns
    ///
    /// * `usize` - The capacity of the stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack: StaticStack<i32> = StaticStack::new(10);
    /// assert_eq!(stack.get_capacity(), 10);
    /// ```
    pub fn get_capacity(&self) -> usize {
        self.elements.len()
    }

    /// Creates a new StaticStack from an array.
    ///
    /// # Arguments
    ///
    /// * `array` - The array to create the StaticStack from.
    ///
    /// # Returns
    ///
    /// * `StaticStack` - The created StaticStack.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let array = [1, 2, 3];
    /// let stack = StaticStack::from_array(&array);
    /// assert_eq!(stack.len(), 3);
    /// assert_eq!(stack.peek(), Some(&3));
    /// ```
    pub fn from_array(array: &[T]) -> Self
    where
        T: Clone,
    {
        let mut stack = StaticStack::new(array.len());
        for item in array {
            stack.push(item.clone());
        }
        stack
    }

    /// Adds multiple elements to the top of the stack.
    ///
    /// # Arguments
    ///
    /// * `items` - The items to add to the stack.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack = StaticStack::new(10);
    /// stack.push_many(&[1, 2, 3]);
    /// assert_eq!(stack.len(), 3);
    /// assert_eq!(stack.peek(), Some(&3));
    /// ```
    pub fn push_many(&mut self, items: &[T])
    where
        T: Clone,
    {
        for item in items {
            self.push(item.clone());
        }
    }

    /// Removes multiple elements from the top of the stack.
    ///
    /// # Arguments
    ///
    /// * `count` - The number of elements to remove.
    ///
    /// # Returns
    ///
    /// * `Some(Vec<T>)` - A vector containing the removed elements.
    /// * `None` - If the stack does not contain enough elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std_only::StaticStack;
    ///
    /// let mut stack = StaticStack::from_array(&[1, 2, 3]);
    /// let popped = stack.pop_many(2);
    /// assert_eq!(popped, Some(vec![2, 3]));
    /// assert_eq!(stack.len(), 1);
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    pub fn pop_many(&mut self, count: usize) -> Option<Vec<T>> {
        if self.top >= count {
            let start = self.top - count;
            let result = self.elements[start..self.top]
                .iter()
                .map(|x| x.clone().unwrap())
                .collect();
            self.top = start;
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
    /// use std_only::StaticStack;
    ///
    /// let mut stack = StaticStack::from_array(&[1, 2, 3]);
    /// let vec = stack.into_vec();
    /// assert_eq!(vec, vec![1, 2, 3]);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.elements.iter().filter_map(|x| x.clone()).collect()
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
    /// use std_only::StaticStack;
    ///
    /// let array = [1, 2, 3];
    /// let stack = StaticStack::from_array(&array);
    /// let boxed_slice = stack.into_boxed_slice();
    /// assert_eq!(&*boxed_slice, &array);
    /// ```
    pub fn into_boxed_slice(self) -> Box<[T]> {
        self.elements
            .iter()
            .filter_map(|x| x.clone())
            .collect::<Vec<T>>()
            .into_boxed_slice()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_stack_is_empty() {
        let stack: StaticStack<i32> = StaticStack::new(10);
        assert_eq!(stack.is_empty(), true);
    }

    #[test]
    fn test_push_to_stack() {
        let mut stack = StaticStack::new(10);
        stack.push(1);
        assert_eq!(stack.is_empty(), false);
        assert_eq!(stack.len(), 1);
        assert_eq!(stack.peek(), Some(&1));
    }

    #[test]
    fn test_pop_from_stack() {
        let mut stack = StaticStack::new(10);
        stack.push(1);
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.is_empty(), true);
    }

    #[test]
    fn test_peek_at_stack() {
        let mut stack = StaticStack::new(10);
        stack.push(1);
        assert_eq!(stack.peek(), Some(&1));
    }

    #[test]
    fn test_stack_length() {
        let mut stack = StaticStack::new(10);
        stack.push(1);
        stack.push(2);
        stack.push(3);
        assert_eq!(stack.len(), 3);
    }

    #[test]
    fn test_from_array() {
        let array = [1, 2, 3];
        let stack = StaticStack::from_array(&array);
        assert_eq!(stack.len(), 3);
        assert_eq!(stack.peek(), Some(&3));
    }

    #[test]
    fn test_push_many() {
        let mut stack = StaticStack::new(10);
        stack.push_many(&[1, 2, 3]);
        assert_eq!(stack.len(), 3);
        assert_eq!(stack.peek(), Some(&3));
    }

    #[test]
    fn test_pop_many() {
        let mut stack = StaticStack::from_array(&[1, 2, 3]);
        let popped = stack.pop_many(2);
        assert_eq!(popped, Some(vec![2, 3]));
        assert_eq!(stack.len(), 1);
        assert_eq!(stack.peek(), Some(&1));
    }
}
