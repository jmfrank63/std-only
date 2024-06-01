// Contents: Selection sort algorithm.
// - SelectionSort trait
// - Tests for SelectionSort

/// Trait for selection sort algorithm.
/// 
/// # Examples
/// 
/// ```
/// use std_only::SelectionSort;
/// 
/// let mut arr = [4, 2, 3, 1];
/// arr.selection_sort(true);
/// assert_eq!(arr, [1, 2, 3, 4]);
/// ```
pub trait SelectionSort {
    fn selection_sort(&mut self, ascending: bool);
}

impl<T: Ord> SelectionSort for [T] {
    fn selection_sort(&mut self, ascending: bool) {
        let len = self.len();
        for i in 0..len {
            let mut min_max = i;
            for j in i + 1..len {
                if (ascending && self[j] < self[min_max]) || (!ascending && self[j] > self[min_max]) {
                    min_max = j;
                }
            }
            if min_max != i {
                self.swap(i, min_max);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_selection_sort_ascending() {
        let mut arr = [4, 2, 3, 1];
        arr.selection_sort(true);
        assert_eq!(arr, [1, 2, 3, 4]);
    }

    #[test]
    fn test_selection_sort_descending() {
        let mut arr = [1, 2, 3, 4];
        arr.selection_sort(false);
        assert_eq!(arr, [4, 3, 2, 1]);
    }

    #[test]
    fn test_selection_sort_empty() {
        let mut arr: [i32; 0] = [];
        arr.selection_sort(true);
        assert_eq!(arr, []);
    }

    #[test]
    fn test_selection_sort_single() {
        let mut arr = [1];
        arr.selection_sort(true);
        assert_eq!(arr, [1]);
    }
}
