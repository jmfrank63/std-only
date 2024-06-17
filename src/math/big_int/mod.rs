const USIZE_BITS: usize = std::mem::size_of::<usize>() * 8;
const BASE: usize = USIZE_BITS - 2;

#[derive(Debug, Clone)]
pub struct BigInt {
    digits: Vec<usize>,
    negative: bool,
}

impl PartialEq for BigInt {
    fn eq(&self, other: &Self) -> bool {
        self.negative == other.negative && self.digits == other.digits
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.negative != other.negative {
            return Some(if self.negative {
                std::cmp::Ordering::Less
            } else {
                std::cmp::Ordering::Greater
            });
        }

        let ordering = if self.digits.len() != other.digits.len() {
            self.digits.len().cmp(&other.digits.len())
        } else {
            for (a, b) in self.digits.iter().zip(&other.digits).rev() {
                if a != b {
                    return Some(a.cmp(b));
                }
            }
            std::cmp::Ordering::Equal
        };

        if self.negative {
            Some(ordering.reverse())
        } else {
            Some(ordering)
        }
    }
}

impl Default for BigInt {
    fn default() -> Self {
        BigInt {
            digits: vec![0],
            negative: false,
        }
    }
}

impl From<isize> for BigInt {
    fn from(n: isize) -> Self {
        if n == isize::MIN {
            BigInt {
                digits: vec![isize::MAX as usize + 1],
                negative: true,
            }
        } else if n < 0 {
            BigInt {
                digits: vec![(-n) as usize],
                negative: true,
            }
        } else {
            BigInt {
                digits: vec![n as usize],
                negative: false,
            }
        }
    }
}
impl From<usize> for BigInt {
    fn from(n: usize) -> Self {
        BigInt {
            digits: vec![n],
            negative: false,
        }
    }
}

impl From<i32> for BigInt {
    fn from(n: i32) -> Self {
        if n < 0 {
            BigInt {
                digits: vec![(-n) as usize],
                negative: true,
            }
        } else {
            BigInt {
                digits: vec![n as usize],
                negative: false,
            }
        }
    }
}

impl From<u32> for BigInt {
    fn from(n: u32) -> Self {
        BigInt {
            digits: vec![n as usize],
            negative: false,
        }
    }
}

impl From<i64> for BigInt {
    fn from(n: i64) -> Self {
        let base = BASE as i64;
        let mut digits = Vec::new();
        let mut num = n.abs();
        while num > 0 {
            digits.push((num % base) as usize);
            num /= base;
        }
        BigInt {
            digits,
            negative: n < 0,
        }
    }
}

impl From<u64> for BigInt {
    fn from(n: u64) -> Self {
        let base = 1 << BASE;
        let mut digits = Vec::new();
        let mut num = n;
        while num > 0 {
            digits.push((num % base) as usize);
            num /= base as u64;
        }
        BigInt {
            digits,
            negative: false,
        }
    }
}

impl From<Vec<usize>> for BigInt {
    fn from(digits: Vec<usize>) -> Self {
        // Remove leading zeros
        let mut digits = digits;
        while digits.len() > 1 && *digits.last().unwrap() == 0 {
            digits.pop();
        }
        BigInt {
            digits,
            negative: false,
        }
    }
}

impl std::ops::Add for BigInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let length = if self.digits.len() >= rhs.digits.len() {
            (self.digits.len(), rhs.digits.len())
        } else {
            (rhs.digits.len(), self.digits.len())
        };
        let max_len = length.0.max(length.1);
        if self.negative == rhs.negative {
            // Adding numbers with the same sign
            let mut result = Vec::with_capacity(max_len);
            let mut carry = 0;

            for i in 0..max_len {
                let a = if i < length.0 { self.digits[i] } else { 0 };
                let b = if i < length.1 { rhs.digits[i] } else { 0 };

                let (sum, overflow1) = a.overflowing_add(b);
                let (sum, overflow2) = sum.overflowing_add(carry);
                carry = (overflow1 || overflow2) as usize;
                result.push(sum);
            }

            if carry > 0 {
                result.push(carry);
            }

            // Remove leading zeros
            while result.len() > 1 && *result.last().unwrap() == 0 {
                result.pop();
            }

            BigInt {
                digits: result,
                negative: self.negative,
            }
        } else {
            // Subtracting numbers with different signs
            if self.abs() >= rhs.abs() {
                // Case 1: Positive larger - Negative smaller
                // Case 2: Negative larger - Positive smaller
                let (larger, smaller, negative) = (&self, &rhs, self.negative);
                subtract_bigints(larger, smaller, negative, max_len)
            } else {
                // Case 3: Positive smaller - Negative larger
                // Case 4: Negative smaller - Positive larger
                let (larger, smaller, negative) = (&rhs, &self, !rhs.negative);
                subtract_bigints(larger, smaller, negative, max_len)
            }
        }
    }
}

fn subtract_bigints(larger: &BigInt, smaller: &BigInt, negative: bool, max_len: usize) -> BigInt {
    let len1 = larger.digits.len();
    let len2 = smaller.digits.len();

    let mut result = Vec::with_capacity(max_len);
    let mut borrow = 0;

    for i in 0..max_len {
        let a = if i < len1 { larger.digits.get(i).copied().unwrap_or(0) } else { 0 };
        let b = if i < len2 { smaller.digits.get(i).copied().unwrap_or(0) } else { 0 };

        let (sub, overflow) = a.overflowing_sub(b.wrapping_add(borrow));
        borrow = overflow as usize;
        result.push(sub);
    }

    // Handle remaining borrow
    if borrow > 0 {
        for digit in result.iter_mut().rev() {
            if *digit == 0 {
                *digit = usize::MAX;
            } else {
                *digit = digit.wrapping_sub(1);
                break;
            }
        }
    }

    // Remove leading zeros
    while result.len() > 1 && *result.last().unwrap() == 0 {
        result.pop();
    }

    if result.len() == 1 && result[0] == 0 {
        BigInt::default()
    } else {
        BigInt {
            digits: result,
            negative,
        }
    }
}

impl BigInt {
    fn abs(&self) -> Self {
        let abs_digits = self.digits.clone();
        Self {
            digits: abs_digits,
            negative: false,
        }
    }
}



impl std::ops::Neg for BigInt {
    type Output = Self;

    fn neg(mut self) -> Self {
        self.negative = !self.negative;
        // Ensure zero is always positive
        if self.digits == vec![0] {
            self.negative = false;
        }
        self
    }
}

impl std::ops::Sub for BigInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self + -rhs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod test_add {

        use super::*;
        #[test]
        fn test_default() {
            let bigint = BigInt::default();
            assert_eq!(bigint.digits, vec![0]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_isize() {
            let bigint = BigInt::from(-42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, true);

            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_usize() {
            let bigint = BigInt::from(usize::MAX);
            assert_eq!(bigint.digits, vec![usize::MAX]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_i32() {
            let bigint = BigInt::from(-42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, true);

            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_u32() {
            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_i64() {
            let bigint = BigInt::from(-42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, true);

            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);

            let bigint = BigInt::from(isize::MIN);
            assert_eq!(bigint.digits, vec![isize::MIN as usize]);
            assert_eq!(bigint.negative, true);
        }

        #[test]
        fn test_from_u64() {
            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);

            let bigint = BigInt::from(1_000_000_000_000_000_000usize);
            assert_eq!(bigint.digits, vec![1000000000000000000]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_vec() {
            let bigint = BigInt::from(vec![42, 42]);
            assert_eq!(bigint.digits, vec![42, 42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_vec_leading_zeros() {
            let bigint = BigInt::from(vec![42, 42, 0, 0]);
            assert_eq!(bigint.digits, vec![42, 42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_vec_zero() {
            let bigint = BigInt::from(vec![0, 0, 0, 0]);
            assert_eq!(bigint.digits, vec![0]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_vec_mixed_zeros() {
            let bigint = BigInt::from(vec![0, 42, 0, 42, 0, 0]);
            assert_eq!(bigint.digits, vec![0, 42, 0, 42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_vec_zero_with_leading_zeros() {
            let bigint = BigInt::from(vec![0, 0, 0, 0]);
            assert_eq!(bigint.digits, vec![0]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_negative_zero_not_allowed() {
            let bigint = BigInt::from(-0);
            assert_eq!(bigint.digits, vec![0]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_vec_single_zero() {
            let bigint = BigInt::from(vec![0]);
            assert_eq!(bigint.digits, vec![0]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_add_positive_numbers() {
            let a = BigInt::from(42);
            let b = BigInt::from(42);
            let sum = a + b;
            assert_eq!(sum.digits, vec![84]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_negative_numbers() {
            let a = BigInt::from(-42);
            let b = BigInt::from(-42);
            let sum = a + b;
            assert_eq!(sum.digits, vec![84]);
            assert_eq!(sum.negative, true);
        }

        #[test]
        fn test_add_overflow_single_digit() {
            let a = BigInt {
                digits: vec![usize::MAX, 0],
                negative: false,
            };
            let b = BigInt::from(1);
            let sum = a + b;
            assert_eq!(sum.digits, vec![0, 1]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_overflow_multiple_digits() {
            let a = BigInt {
                digits: vec![usize::MAX, usize::MAX],
                negative: false,
            };
            let b = BigInt::from(1);
            let sum = a + b;
            assert_eq!(sum.digits, vec![0, 0, 1]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_sub_with_borrow_due_to_max_value() {
            let a = BigInt {
                digits: vec![1],
                negative: false,
            };
            let b = BigInt {
                digits: vec![usize::MAX],
                negative: true,
            };
            let difference = a + b;
            assert_eq!(difference.digits, vec![2]);
            assert_eq!(difference.negative, true);
        }
        
        #[test]
        fn test_add_max_usize() {
            let a = BigInt::from(usize::MAX);
            let b = BigInt::from(usize::MAX);
            let sum = a + b;
            assert_eq!(sum.digits, vec![usize::MAX - 1, 1]);
            assert_eq!(sum.negative, false);
        }

        // Add tests for adding positive and negative numbers
        #[test]
        fn test_add_positive_negative() {
            let a = BigInt::from(42);
            let b = BigInt::from(-42);
            let sum = a + b;
            assert_eq!(sum.digits, vec![0]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_negative_positive() {
            let a = BigInt::from(-42);
            let b = BigInt::from(42);
            let sum = a + b;
            assert_eq!(sum.digits, vec![0]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_negative_positive_overflow() {
            let a = BigInt {
                digits: vec![0, 1],
                negative: false,
            };
            let b = BigInt::from(-1);
            let sum = a + b;
            assert_eq!(sum.digits, vec![usize::MAX]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_positive_negative_overflow() {
            let a = BigInt {
                digits: vec![0, 1],
                negative: true,
            };
            let b = BigInt::from(1);
            let sum = a + b;
            assert_eq!(sum.digits, vec![usize::MAX]);
            assert_eq!(sum.negative, true);
        }

        #[test]
        fn test_add_large_numbers_no_overflow() {
            let a = BigInt {
                digits: vec![123456789, 987654321, 123456789],
                negative: false,
            };
            let b = BigInt {
                digits: vec![987654321, 123456789, 987654321],
                negative: false,
            };
            let sum = a + b;
            assert_eq!(sum.digits, vec![1111111110, 1111111110, 1111111110]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_large_numbers_with_overflow() {
            let a = BigInt {
                digits: vec![usize::MAX - 1, usize::MAX - 1, usize::MAX - 1],
                negative: false,
            };
            let b = BigInt {
                digits: vec![2, 2, 2],
                negative: false,
            };
            let sum = a + b;
            assert_eq!(sum.digits, vec![0, 1, 1, 1]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_subtract_large_numbers() {
            let a = BigInt {
                digits: vec![usize::MAX, usize::MAX, usize::MAX],
                negative: false,
            };
            let b = BigInt {
                digits: vec![1, 1, 1],
                negative: true,
            };
            let diff = a + b;
            assert_eq!(
                diff.digits,
                vec![usize::MAX - 1, usize::MAX - 1, usize::MAX - 1],
            );
            assert_eq!(diff.negative, false);
        }

        #[test]
        fn test_subtract_large_numbers_with_borrow() {
            let a = BigInt {
                digits: vec![0, 0, usize::MAX],
                negative: false,
            };
            let b = BigInt {
                digits: vec![1, 1, 1],
                negative: true,
            };
            let diff = a + b;
            assert_eq!(
                diff.digits,
                vec![usize::MAX, usize::MAX - 1, usize::MAX - 2]
            );
            assert_eq!(diff.negative, false);
        }

        #[test]
        fn test_mixed_sign_operations() {
            let a = BigInt {
                digits: vec![usize::MAX, 0, 123456789],
                negative: true,
            };
            let b = BigInt {
                digits: vec![1, 0, 987654321],
                negative: false,
            };
            let sum = a + b;
            assert_eq!(sum.digits, vec![2, usize::MAX, 864197531]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_mixed_sign_operations_2() {
            let a = BigInt {
                digits: vec![123456789, 987654321, 123456789],
                negative: true,
            };
            let b = BigInt {
                digits: vec![987654321, 123456789, 987654321],
                negative: false,
            };
            let sum = a + b;
            assert_eq!(
                sum.digits,
                vec![864197532, usize::MAX - 864197532 + 1, 864197531]
            );
            assert_eq!(sum.negative, false);
        }
    }

    mod test_neg {
        use super::*;
        use std::ops::Neg;

        #[test]
        fn test_neg_positive() {
            let bigint = BigInt::from(42).neg();
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, true);
        }

        #[test]
        fn test_neg_negative() {
            let bigint = BigInt::from(-42).neg();
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_neg_zero() {
            let bigint = BigInt::default().neg();
            assert_eq!(bigint.digits, vec![0]);
            assert_eq!(bigint.negative, false);
        }
    }

    mod test_sub {
        use super::*;

        #[test]
        fn test_default() {
            let bigint = BigInt::default();
            assert_eq!(bigint.digits, vec![0]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_isize_negative() {
            let bigint = BigInt::from(-42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, true);
        }

        #[test]
        fn test_from_isize_positive() {
            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_usize() {
            let bigint = BigInt::from(usize::MAX);
            assert_eq!(bigint.digits, vec![usize::MAX]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_i32_negative() {
            let bigint = BigInt::from(-42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, true);
        }

        #[test]
        fn test_from_i32_positive() {
            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_u32() {
            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_i64_negative() {
            let bigint = BigInt::from(-42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, true);
        }

        #[test]
        fn test_from_i64_positive() {
            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_i64_min() {
            let bigint = BigInt::from(isize::MIN);
            assert_eq!(bigint.digits, vec![isize::MIN as usize]);
            assert_eq!(bigint.negative, true);
        }

        #[test]
        fn test_from_u64() {
            let bigint = BigInt::from(42);
            assert_eq!(bigint.digits, vec![42]);
            assert_eq!(bigint.negative, false);

            let bigint = BigInt::from(1_000_000_000_000_000_000usize);
            assert_eq!(bigint.digits, vec![1000000000000000000]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_from_vec() {
            let bigint = BigInt::from(vec![42, 42]);
            assert_eq!(bigint.digits, vec![42, 42]);
            assert_eq!(bigint.negative, false);
        }

        #[test]
        fn test_add_positive_numbers() {
            let a = BigInt::from(42);
            let b = BigInt::from(42);
            let sum = a + b;
            assert_eq!(sum.digits, vec![84]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_negative_numbers() {
            let a = BigInt::from(-42);
            let b = BigInt::from(-42);
            let sum = a + b;
            assert_eq!(sum.digits, vec![84]);
            assert_eq!(sum.negative, true);
        }

        #[test]
        fn test_add_overflow_single_digit() {
            let a = BigInt {
                digits: vec![usize::MAX, 0],
                negative: false,
            };
            let b = BigInt::from(1);
            let sum = a + b;
            assert_eq!(sum.digits, vec![0, 1]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_overflow_multiple_digits() {
            let a = BigInt {
                digits: vec![usize::MAX, usize::MAX],
                negative: false,
            };
            let b = BigInt::from(1);
            let sum = a + b;
            assert_eq!(sum.digits, vec![0, 0, 1]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_max_usize() {
            let a = BigInt::from(usize::MAX);
            let b = BigInt::from(usize::MAX);
            let sum = a + b;
            assert_eq!(sum.digits, vec![usize::MAX - 1, 1]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_positive_negative() {
            let a = BigInt::from(42);
            let b = BigInt::from(-42);
            let sum = a + b;
            assert_eq!(sum.digits, vec![0]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_negative_positive() {
            let a = BigInt::from(-42);
            let b = BigInt::from(42);
            let sum = a + b;
            assert_eq!(sum.digits, vec![0]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_negative_positive_overflow() {
            let a = BigInt {
                digits: vec![0, 1],
                negative: false,
            };
            let b = BigInt::from(-1);
            let sum = a + b;
            assert_eq!(sum.digits, vec![usize::MAX]);
            assert_eq!(sum.negative, false);
        }

        #[test]
        fn test_add_positive_negative_overflow() {
            let a = BigInt {
                digits: vec![0, 1],
                negative: true,
            };
            let b = BigInt::from(1);
            let sum = a + b;
            assert_eq!(sum.digits, vec![usize::MAX]);
            assert_eq!(sum.negative, true);
        }
    }

}
