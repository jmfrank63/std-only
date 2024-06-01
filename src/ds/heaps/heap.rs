// Contents:
// - Heap struct
// - Implementation of Heap
// - Tests for Heap

/// An enum representing the type of a Heap.
#[derive(Debug, PartialEq)]
pub enum HeapType {
    Min,
    Max,
}

impl Default for HeapType {
    /// Default implementation for HeapType.
    ///
    /// Creates a new HeapType with Min.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::HeapType;
    ///
    /// let heap_type: HeapType = HeapType::default();
    /// assert_eq!(heap_type, HeapType::Min);
    /// ```
    fn default() -> Self {
        HeapType::Min
    }
}

/// A Heap data structure.
///
/// A heap is a data structure that allows elements to be added and removed in a specific order.
///
/// # Examples
///
/// ```
/// use studylib::ds::heaps::heap::{Heap, HeapType};
///
/// let mut heap = Heap::new(HeapType::Min);
/// heap.push(1);
/// heap.push(2);
/// heap.push(3);
/// assert_eq!(heap.peek(), Some(&1));
/// assert_eq!(heap.pop(), Some(1));
/// assert_eq!(heap.pop(), Some(2));
/// assert_eq!(heap.pop(), Some(3));
/// assert_eq!(heap.pop(), None);
/// ```
#[derive(Debug)]
pub struct Heap<T> {
    elements: Vec<T>,
    heap_type: HeapType,
}
impl<T: Clone> Default for Heap<T> {
    /// Creates a new empty Heap
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::Heap;
    ///
    /// let mut heap: Heap<i32> = Heap::default();
    /// assert!(heap.is_empty());
    /// ```
    fn default() -> Self {
        Self {
            elements: Vec::new(),
            heap_type: HeapType::default(),
        }
    }
}

impl<T: Ord + Clone> Heap<T> {
    /// Creates a new Heap.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap: Heap<i32> = Heap::new(HeapType::Min);
    /// assert!(heap.is_empty());
    /// ```
    pub fn new(heap_type: HeapType) -> Self {
        Self {
            elements: Vec::new(),
            heap_type,
        }
    }

    /// Pushes a new element onto the heap.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap = Heap::new(HeapType::Min);
    /// heap.push(1);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn push(&mut self, value: T) {
        match self.heap_type {
            HeapType::Min => {
                self.elements.push(value);
                self.heapify_up_min(self.elements.len() - 1);
            }
            HeapType::Max => {
                self.elements.push(value);
                self.heapify_up_max(self.elements.len() - 1);
            }
        }
    }

    fn heapify_up_min(&mut self, idx: usize) {
        let mut child = idx;
        while child > 0 {
            let parent = (child - 1) / 2;
            if self.elements[child] < self.elements[parent] {
                self.elements.swap(child, parent);
            } else {
                break;
            }
            child = parent;
        }
    }

    fn heapify_up_max(&mut self, idx: usize) {
        let mut child = idx;
        while child > 0 {
            let parent = (child - 1) / 2;
            if self.elements[child] > self.elements[parent] {
                self.elements.swap(child, parent);
            } else {
                break;
            }
            child = parent;
        }
    }

    /// Pushes all elements from an array onto the heap.
    ///
    /// # Arguments
    ///
    /// * `array` - The array to push onto the heap.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap = Heap::new(HeapType::Min);
    /// heap.push_all_from_array(&[1, 2, 3]);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn push_all_from_array(&mut self, array: &[T]) {
        for item in array {
            self.push(item.clone());
        }
    }

    /// Pushes all elements from a vector onto the heap.
    ///
    /// # Arguments
    ///
    /// * `vec` - The vector to push onto the heap.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap = Heap::new(HeapType::Min);
    /// heap.push_all_from_vec(vec![1, 2, 3]);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn push_all_from_vec(&mut self, vec: Vec<T>) {
        for item in vec {
            self.push(item);
        }
    }

    /// Removes the top element of the heap.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap = Heap::new(HeapType::Min);
    /// heap.push(1);
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.elements.is_empty() {
            None
        } else {
            let root = self.elements.swap_remove(0);
            if !self.elements.is_empty() {
                match self.heap_type {
                    HeapType::Min => self.heapify_down_min(0),
                    HeapType::Max => self.heapify_down_max(0),
                }
            }
            Some(root)
        }
    }

    fn heapify_down_min(&mut self, idx: usize) {
        let mut parent = idx;

        loop {
            let left_child = 2 * parent + 1;
            let right_child = 2 * parent + 2;
            let mut smallest = parent;

            if left_child < self.elements.len()
                && self.elements[left_child] < self.elements[smallest]
            {
                smallest = left_child;
            }

            if right_child < self.elements.len()
                && self.elements[right_child] < self.elements[smallest]
            {
                smallest = right_child;
            }

            if smallest == parent {
                break;
            }

            self.elements.swap(parent, smallest);
            parent = smallest;
        }
    }

    fn heapify_down_max(&mut self, idx: usize) {
        let mut parent = idx;

        loop {
            let left_child = 2 * parent + 1;
            let right_child = 2 * parent + 2;
            let mut largest = parent;

            if left_child < self.elements.len()
                && self.elements[left_child] > self.elements[largest]
            {
                largest = left_child;
            }

            if right_child < self.elements.len()
                && self.elements[right_child] > self.elements[largest]
            {
                largest = right_child;
            }

            if largest == parent {
                break;
            }

            self.elements.swap(parent, largest);
            parent = largest;
        }
    }

    /// Removes multiple elements from the heap.
    ///
    /// # Arguments
    ///
    /// * `count` - The number of elements to remove.
    ///
    /// # Returns
    ///
    /// * `Vec<T>` - The removed elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap = Heap::new(HeapType::Min);
    /// heap.push(1);
    /// heap.push(2);
    /// heap.push(3);
    /// assert_eq!(heap.pop_multiple(2), vec![1, 2]);
    /// assert_eq!(heap.pop_multiple(2), vec![3]);
    /// ```
    pub fn pop_multiple(&mut self, count: usize) -> Vec<T> {
        let mut result = Vec::new();
        for _ in 0..count {
            if let Some(item) = self.pop() {
                result.push(item);
            } else {
                break;
            }
        }
        result
    }

    /// Returns a reference to the
    /// top element of the heap.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap = Heap::new(HeapType::Min);
    /// heap.push(1);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.elements.first()
    }

    /// Returns the minimum element of the heap.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap = Heap::new(HeapType::Min);
    /// heap.push(1);
    /// heap.push(2);
    /// heap.push(3);
    /// assert_eq!(heap.min(), Some(&1));
    /// ```
    pub fn min(&self) -> Option<&T> {
        match self.heap_type {
            HeapType::Min => self.peek(),
            HeapType::Max => self.elements.iter().min(),
        }
    }

    /// Returns the maximum element of the heap.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap = Heap::new(HeapType::Max);
    /// heap.push(1);
    /// heap.push(2);
    /// heap.push(3);
    /// assert_eq!(heap.max(), Some(&3));
    /// ```
    pub fn max(&self) -> Option<&T> {
        match self.heap_type {
            HeapType::Min => self.elements.iter().max(),
            HeapType::Max => self.peek(),
        }
    }

    /// Returns the number of elements in the heap.
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Returns true if the heap is empty.
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Creates a new Heap from an array.
    ///
    /// # Arguments
    ///
    /// * `array` - The array to create the Heap from.
    ///
    /// # Returns
    ///
    /// * `Heap<T>` - The new Heap.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap,HeapType};
    ///
    /// let heap = Heap::from_array(HeapType::Min, &[1, 2, 3]);
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn from_array(heap_type: HeapType, array: &[T]) -> Self {
        let mut heap = Self::new(heap_type);
        for item in array {
            heap.push((*item).clone());
        }
        heap
    }

    /// Creates a new Heap from a vector.
    ///
    /// # Arguments
    ///
    /// * `vec` - The vector to create the Heap from.
    ///
    /// # Returns
    ///
    /// * `Heap<T>` - The new Heap.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap,HeapType};
    ///
    /// let heap = Heap::from_vec(HeapType::Min, vec![1, 2, 3]);
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn from_vec(heap_type: HeapType, vec: Vec<T>) -> Self {
        let mut heap = Self::new(heap_type);
        for item in vec {
            heap.push(item);
        }
        heap
    }

    /// Inverts the Heap.
    ///
    /// # Returns
    ///
    /// * `Heap<T>` - The inverted Heap.
    ///
    /// # Examples
    ///
    /// ```
    /// use studylib::ds::heaps::heap::{Heap, HeapType};
    ///
    /// let mut heap = Heap::new(HeapType::Min);
    /// heap.push(3);
    /// heap.push(2);
    /// heap.push(1);
    /// let inverted_heap = heap.invert();
    /// assert_eq!(inverted_heap.peek(), Some(&3));
    /// ```
    pub fn invert(&self) -> Heap<T> {
        let new_heap_type = match self.heap_type {
            HeapType::Min => HeapType::Max,
            HeapType::Max => HeapType::Min,
        };

        let mut new_heap = Heap::new(new_heap_type);
        for item in &self.elements {
            new_heap.push(item.clone());
        }
        new_heap
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default() {
        let heap: Heap<i32> = Heap::default();
        assert!(heap.is_empty());
    }

    #[test]
    fn test_heapify_up_min() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(3);
        heap.push(2);
        heap.push(1);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_heapify_up_max() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        assert_eq!(heap.peek(), Some(&3));
    }

    #[test]
    fn test_heapify_down_min() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(3);
        heap.push(2);
        heap.push(1);
        heap.pop();
        assert_eq!(heap.peek(), Some(&2));
    }

    #[test]
    fn test_heapify_down_max() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        heap.pop();
        assert_eq!(heap.peek(), Some(&2));
    }

    #[test]
    fn test_heapify_up_min_with_duplicates() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(3);
        heap.push(2);
        heap.push(1);
        heap.push(1);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_heapify_up_max_with_duplicates() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        heap.push(3);
        assert_eq!(heap.peek(), Some(&3));
    }

    #[test]
    fn test_heapify_down_min_with_duplicates() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(3);
        heap.push(2);
        heap.push(1);
        heap.push(1);
        heap.pop();
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_heapify_down_max_with_duplicates() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        heap.push(3);
        heap.pop();
        assert_eq!(heap.peek(), Some(&3));
    }

    #[test]
    fn test_heapify_up_min_with_same_priority() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(1);
        heap.push(1);
        heap.push(1);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_heapify_up_max_with_same_priority() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(1);
        heap.push(1);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_heapify_down_min_with_same_priority() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(1);
        heap.push(1);
        heap.push(1);
        heap.pop();
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_heapify_down_max_with_same_priority() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(1);
        heap.push(1);
        heap.pop();
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_push_min() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_pop_min() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), Some(3));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_push_max() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        assert_eq!(heap.peek(), Some(&3));
    }

    #[test]
    fn test_pop_max() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        assert_eq!(heap.pop(), Some(3));
        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_peek() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(1);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_min_in_min_heap() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(3);
        heap.push(2);
        heap.push(1);
        assert_eq!(heap.min(), Some(&1));
    }

    #[test]
    fn test_max_in_min_heap() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(3);
        heap.push(2);
        heap.push(1);
        assert_eq!(heap.max(), Some(&3));
    }

    #[test]
    fn test_min_in_max_heap() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        assert_eq!(heap.min(), Some(&1));
    }

    #[test]
    fn test_max_in_max_heap() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        assert_eq!(heap.max(), Some(&3));
    }
    #[test]
    fn test_len() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        assert_eq!(heap.len(), 3);
    }

    #[test]
    fn test_is_empty() {
        let heap: Heap<i32> = Heap::new(HeapType::Min);
        assert!(heap.is_empty());
    }

    #[test]
    fn test_from_array_min_heap() {
        let array = [3, 2, 1];
        let heap = Heap::from_array(HeapType::Min, &array);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_from_array_max_heap() {
        let array = [1, 2, 3];
        let heap = Heap::from_array(HeapType::Max, &array);
        assert_eq!(heap.peek(), Some(&3));
    }

    #[test]
    fn test_from_vec_min_heap() {
        let vec = vec![3, 2, 1];
        let heap = Heap::from_vec(HeapType::Min, vec);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_from_vec_max_heap() {
        let vec = vec![1, 2, 3];
        let heap = Heap::from_vec(HeapType::Max, vec);
        assert_eq!(heap.peek(), Some(&3));
    }

    #[test]
    fn test_invert_min_to_max() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push(3);
        heap.push(2);
        heap.push(1);
        let inverted_heap = heap.invert();
        assert_eq!(inverted_heap.peek(), Some(&3));
    }

    #[test]
    fn test_invert_max_to_min() {
        let mut heap = Heap::new(HeapType::Max);
        heap.push(1);
        heap.push(2);
        heap.push(3);
        let inverted_heap = heap.invert();
        assert_eq!(inverted_heap.peek(), Some(&1));
    }

    #[test]
    fn test_push_all_from_array() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push_all_from_array(&[3, 2, 1]);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_push_all_from_vec() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push_all_from_vec(vec![3, 2, 1]);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_pop_multiple() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push_all_from_array(&[3, 2, 1]);
        let popped = heap.pop_multiple(2);
        assert_eq!(popped, vec![1, 2]);
    }

    #[test]
    fn test_pop_multiple_more_than_size() {
        let mut heap = Heap::new(HeapType::Min);
        heap.push_all_from_array(&[3, 2, 1]);
        let popped = heap.pop_multiple(5);
        assert_eq!(popped, vec![1, 2, 3]);
    }
}
