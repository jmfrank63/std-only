// Contents: Bubble sort algorithm.
// - BubbleSort trait
// - Tests for BubbleSort

/// Trait for bubble sort algorithm.
/// 
/// # Examples
/// 
/// ```
/// use studylib::alg::sort::BubbleSort;
/// 
/// let mut arr = [4, 2, 3, 1];
/// arr.bubble_sort(true);
/// assert_eq!(arr, [1, 2, 3, 4]);
/// ```
pub trait BubbleSort {
    fn bubble_sort(&mut self, ascending: bool);
}

impl<T: Ord> BubbleSort for [T] {
    fn bubble_sort(&mut self, ascending: bool) {
        let len = self.len();
        for i in 0..len {
            for j in 0..len - i - 1 {
                if (ascending && self[j] > self[j + 1]) || (!ascending && self[j] < self[j + 1]) {
                    self.swap(j, j + 1);
                }
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bubble_sort_ascending() {
        let mut arr = [4, 2, 3, 1];
        arr.bubble_sort(true);
        assert_eq!(arr, [1, 2, 3, 4]);
    }

    #[test]
    fn test_bubble_sort_descending() {
        let mut arr = [1, 2, 3, 4];
        arr.bubble_sort(false);
        assert_eq!(arr, [4, 3, 2, 1]);
    }

    #[test]
    fn test_bubble_sort_empty() {
        let mut arr: [i32; 0] = [];
        arr.bubble_sort(true);
        assert_eq!(arr, []);
    }

    #[test]
    fn test_bubble_sort_single() {
        let mut arr = [1];
        arr.bubble_sort(true);
        assert_eq!(arr, [1]);
    }

    #[test]
    fn test_bubble_sort_already_sorted() {
        let mut arr = [1, 2, 3, 4];
        arr.bubble_sort(true);
        assert_eq!(arr, [1, 2, 3, 4]);
    }
}
