// A dynamic stack implementation in Rust

pub struct Stack<T> {
    #[cfg(feature = "static")]
    elements: Box<[Option<T>]>,
    #[cfg(feature = "static")]
    top: usize,
    #[cfg(not(feature = "static"))]
    elements: Vec<T>,
}

#[cfg(not(feature = "static"))]
impl<T: Clone> Default for Stack<T> {
    fn default() -> Self {
        Stack {
            elements: Vec::new(),
        }
    }
}

#[cfg(feature = "static")]
impl<T: Clone> Default for Stack<T> {
    fn default() -> Self {
        Stack {
            elements: vec![None; 10].into_boxed_slice(),
            top: 0,
        }
    }
}

#[cfg(not(feature = "static"))]
impl<T: Clone> Stack<T> {
    pub fn new(capacity: usize) -> Self {
        Stack {
            elements: Vec::with_capacity(capacity),
        }
    }

    pub fn push(&mut self, element: T) {
        self.elements.push(element);
    }

    pub fn pop(&mut self) -> Option<T> {
        self.elements.pop()
    }

    pub fn peek(&self) -> Option<&T> {
        self.elements.last()
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
        Stack {
            elements: array.to_vec(),
        }
    }

    pub fn push_many(&mut self, items: &[T])
    where
        T: Clone,
    {
        self.elements.extend_from_slice(items);
    }

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

    pub fn into_vec(self) -> Vec<T> {
        self.elements
    }

    pub fn into_boxed_slice(self) -> Box<[T]> {
        self.elements.into_boxed_slice()
    }
}

#[cfg(feature = "static")]
impl<T: Clone> Stack<T> {
    pub fn new(size: usize) -> Self {
        Self {
            elements: vec![None; size].into_boxed_slice(),
            top: 0,
        }
    }

    // Add the other methods accordingly for an boxed array

    pub fn push(&mut self, element: T) {
        if self.top < self.elements.len() {
            self.elements[self.top] = Some(element);
            self.top += 1;
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.top > 0 {
            self.top -= 1;
            self.elements[self.top].take()
        } else {
            None
        }
    }

    pub fn peek(&self) -> Option<&T> {
        self.elements.get(self.top - 1).and_then(|x| x.as_ref())
    }

    pub fn is_empty(&self) -> bool {
        self.top == 0
    }

    pub fn len(&self) -> usize {
        self.top
    }

    pub fn from_array(array: &[T]) -> Self
    where
        T: Clone,
    {
        let mut stack = Stack::new(array.len());
        for item in array {
            stack.push(item.clone());
        }
        stack
    }

    pub fn push_many(&mut self, items: &[T])
    where
        T: Clone,
    {
        for item in items {
            self.push(item.clone());
        }
    }

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

    pub fn into_vec(self) -> Vec<T> {
        self.elements.iter().filter_map(|x| x.clone()).collect()
    }

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

    #[cfg(not(feature = "static"))]
    mod dynamic_tests {

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

    #[cfg(feature = "static")]
    mod static_tests {
        use super::*;

        #[test]
        fn test_new_stack_is_empty() {
            let stack: Stack<i32> = Stack::new(10);
            assert_eq!(stack.is_empty(), true);
        }

        #[test]
        fn test_push_to_stack() {
            let mut stack = Stack::new(10);
            stack.push(1);
            assert_eq!(stack.is_empty(), false);
            assert_eq!(stack.len(), 1);
            assert_eq!(stack.peek(), Some(&1));
        }

        #[test]
        fn test_pop_from_stack() {
            let mut stack = Stack::new(10);
            stack.push(1);
            assert_eq!(stack.pop(), Some(1));
            assert_eq!(stack.is_empty(), true);
        }

        #[test]
        fn test_peek_at_stack() {
            let mut stack = Stack::new(10);
            stack.push(1);
            assert_eq!(stack.peek(), Some(&1));
        }

        #[test]
        fn test_stack_length() {
            let mut stack = Stack::new(10);
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
            let mut stack = Stack::new(10);
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
}
