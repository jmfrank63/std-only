// Contents:
// - Heap struct
// - Implementation of Heap
// - Tests for Heap

pub use super::Heap;


#[derive(Debug)]
pub struct BinaryMinHeap<T> {
    elements: Vec<T>,
}

impl<T: Ord> Default for BinaryMinHeap<T> {
    /// Creates a new empty Heap
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::BinaryMinHeap;
    ///
    /// let mut heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
    /// assert!(heap.is_empty());
    /// ```
    fn default() -> Self {
        Self {
            elements: Vec::new(),
        }
    }
}

impl<T: Ord> Heap<T> for BinaryMinHeap<T> {
    fn insert(&mut self, item: T) {
        self.elements.push(item);
        let mut i = self.elements.len() - 1;
        while i > 0 {
            let parent = (i - 1) / 2;
            if self.elements[i] >= self.elements[parent] {
                break;
            }
            self.elements.swap(i, parent);
            i = parent;
        }
    }

    fn remove(&mut self) -> Option<T> {
        if self.elements.is_empty() {
            return None;
        }
        let result = Some(self.elements.swap_remove(0));
        let mut i = 0;
        while i < self.elements.len() {
            let left = 2 * i + 1;
            let right = 2 * i + 2;
            let mut smallest = i;
            if left < self.elements.len() && self.elements[left] < self.elements[smallest] {
                smallest = left;
            }
            if right < self.elements.len() && self.elements[right] < self.elements[smallest] {
                smallest = right;
            }
            if smallest == i {
                break;
            }
            self.elements.swap(i, smallest);
            i = smallest;
        }
        result
    }

    fn peek(&self) -> Option<&T> {
        self.elements.get(0)
    }

    fn len(&self) -> usize {
        self.elements.len()
    }

    fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    fn merge(&mut self, other: Self) {
        self.elements.extend(other.elements);
        self.elements.sort();
    }
}

impl<T: Ord> BinaryMinHeap<T> {
    /// Merges two BinaryMinHeaps into one.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::BinaryMinHeap;
    ///
    /// let mut heap1: BinaryMinHeap<i32> = BinaryMinHeap::default();
    /// heap1.insert(1);
    /// heap1.insert(3);
    /// heap1.insert(5);
    /// let mut heap2: BinaryMinHeap<i32> = BinaryMinHeap::default();
    /// heap2.insert(2);
    /// heap2.insert(4);
    /// heap2.insert(6);
    /// heap1.merge(heap2);
    /// assert_eq!(heap1.len(), 6);
    /// assert_eq!(heap1.peek(), Some(&1));
    /// ```
    pub fn merge(&mut self, other: Self) {
        Heap::merge(self, other)
    }

    /// Returns a reference to the smallest element in the heap.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::BinaryMinHeap;
    ///
    /// let mut heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
    /// heap.insert(1);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        Heap::peek(self)
    }

    /// Returns the number of elements in the heap.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::BinaryMinHeap;
    ///
    /// let mut heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
    /// heap.insert(1);
    /// heap.insert(2);
    /// assert_eq!(heap.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        Heap::len(self)
    }

    /// Inserts an element into the heap.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::BinaryMinHeap;
    ///
    /// let mut heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
    /// heap.insert(3);
    /// heap.insert(1);
    /// heap.insert(2);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn insert(&mut self, item: T) {
        Heap::insert(self, item)
    }

    /// Removes the smallest element from the heap and returns it.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::BinaryMinHeap;
    ///
    /// let mut heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
    /// heap.insert(3);
    /// heap.insert(1);
    /// heap.insert(2);
    /// assert_eq!(heap.remove(), Some(1));
    /// assert_eq!(heap.remove(), Some(2));
    /// assert_eq!(heap.remove(), Some(3));
    /// assert_eq!(heap.remove(), None);
    /// ```
    pub fn remove(&mut self) -> Option<T> {
        Heap::remove(self)
    }
    
    /// Checks if the heap is empty.
    ///
    /// Examples
    ///
    /// ```
    /// use studylib::ds::heaps::BinaryMinHeap;
    ///
    /// let heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
    /// assert!(heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        Heap::is_empty(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_heap_default() {
        let heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
        assert!(heap.is_empty());
    }

    #[test]
    fn test_heap_insert() {
        let mut heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
        heap.insert(3);
        heap.insert(1);
        heap.insert(2);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_heap_remove() {
        let mut heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
        heap.insert(3);
        heap.insert(1);
        heap.insert(2);
        assert_eq!(heap.remove(), Some(1));
        assert_eq!(heap.remove(), Some(2));
        assert_eq!(heap.remove(), Some(3));
        assert_eq!(heap.remove(), None);
    }

    #[test]
    fn test_heap_peek() {
        let mut heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
        heap.insert(1);
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn test_heap_len() {
        let mut heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
        heap.insert(1);
        heap.insert(2);
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn test_heap_is_empty() {
        let heap: BinaryMinHeap<i32> = BinaryMinHeap::default();
        assert!(heap.is_empty());
    }

    #[test]
    fn test_heap_merge() {
        let mut heap1: BinaryMinHeap<i32> = BinaryMinHeap::default();
        heap1.insert(1);
        heap1.insert(3);
        heap1.insert(5);
        let mut heap2: BinaryMinHeap<i32> = BinaryMinHeap::default();
        heap2.insert(2);
        heap2.insert(4);
        heap2.insert(6);
        heap1.merge(heap2);
        assert_eq!(heap1.len(), 6);
        assert_eq!(heap1.peek(), Some(&1));
    }

}
