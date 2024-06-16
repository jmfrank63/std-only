const USIZE_BITS: usize = std::mem::size_of::<usize>() * 8;
const BASE: usize = USIZE_BITS - 2;

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct BigInt {
    digits: Vec<usize>,
    negative: bool,
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
        BigInt {
            digits,
            negative: false,
        }
    }
}

impl std::ops::Add for BigInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let result = if self.negative == rhs.negative {
            let len1 = self.digits.len();
            let len2 = rhs.digits.len();
            let max_len = len1.max(len2);

            let mut result = Vec::with_capacity(max_len);
            let mut carry = 0;

            for i in 0..max_len {
                let a = if i < len1 { self.digits[i] } else { 0 };
                let b = if i < len2 { rhs.digits[i] } else { 0 };

                let sum = a.wrapping_add(b).wrapping_add(carry);
                carry = (sum < a || (carry > 0 && sum == a)) as usize;
                result.push(sum);

                if a == 0 && b == 0 && carry == 0 {
                    break;
                }
            }

            if carry > 0 {
                result.push(carry);
            }

            // Remove leading zeros
            while result.len() > 1 && *result.last().unwrap() == 0 {
                result.pop();
            }
            result
        } else {
            Vec::new()
        };

        // If the result is zero, it should be positive
        if result.len() == 1 && result[0] == 0 {
            return Self::default();
        } 
        
        Self {
            digits: result,
            negative: self.negative,
        }
    }
}

impl std::ops::Sub for BigInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        let mut digits = Vec::new();
        let mut carry = 0;
        if self.negative == rhs.negative {
            // Subtract the two numbers
            for (a, b) in self.digits.iter().zip(&rhs.digits) {
                let diff = a.wrapping_sub(*b).wrapping_sub(carry);
                carry = (diff > *a || (carry > 0 && diff == *a)) as usize;
                digits.push(diff);
            }
            Self {
                digits,
                negative: self.negative,
            }
        } else {
            let result = if rhs.abs() > self.abs() {
                rhs.abs() - self.abs()
            } else {
                self.abs() - rhs.abs()
            };
            result
        }
    }
}

impl BigInt {
    fn abs(&self) -> Self {
        Self {
            digits: self.digits.clone(),
            negative: false,
        }
    }
}

#[cfg(test)]
mod tests {
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
        assert_eq!(sum.negative, true);
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
        assert_eq!(sum.negative, false);
    }
}
