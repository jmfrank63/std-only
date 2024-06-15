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

impl std::ops::Add for BigInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        if self.negative == rhs.negative {
            let mut result = BigInt {
                digits: Vec::new(),
                negative: self.negative,
            };
            let mut carry = 0;

            for (a, b) in self.digits.iter().zip(&rhs.digits) {
                let sum = a.wrapping_add(*b).wrapping_add(carry);
                carry = (sum < *a || (carry > 0 && sum == *a)) as usize;
                result.digits.push(sum);
            }

            let longer_digits = if self.digits.len() > rhs.digits.len() {
                &self.digits[rhs.digits.len()..]
            } else {
                &rhs.digits[self.digits.len()..]
            };

            for &a in longer_digits {
                let sum = a.wrapping_add(carry);
                carry = (sum < a) as usize;
                result.digits.push(sum);
            }

            if carry > 0 {
                result.digits.push(carry);
            }

            if result.is_zero() {
                result.negative = false;
            }

            result
        } else {
            let (larger, smaller, negative) = if self.abs() >= rhs.abs() {
                (&self, &rhs, self.negative)
            } else {
                (&rhs, &self, rhs.negative)
            };

            let mut result = BigInt::default();

            let mut borrow = 0;
            for (i, (a, b)) in larger.digits.iter().zip(smaller.digits.iter()).enumerate() {
                let (sub, overflow) = a.overflowing_sub(*b + borrow);
                borrow = if overflow { 1 } else { 0 };
                result.digits.push(sub);
                println!("Step {}: borrow: {}, result: {:?}", i, borrow, result.digits);
            }

            for (i, &a) in larger.digits.iter().skip(smaller.digits.len()).enumerate() {
                let (sub, overflow) = a.overflowing_sub(borrow);
                borrow = if overflow { 1 } else { 0 };
                result.digits.push(sub);
                println!("Step {}: borrow: {}, result: {:?}", i + smaller.digits.len(), borrow, result.digits);
            }

            // Handle case where borrow is still 1 after the loop
            if borrow > 0 {
                for (i, digit) in result.digits.iter_mut().rev().enumerate() {
                    println!("Borrow step {}: {:?}", i, digit);
                    if *digit == 0 {
                        *digit = usize::MAX;
                    } else {
                        *digit = digit.wrapping_sub(1);
                        break;
                    }
                }
            }

            println!("Result: {:?}", result.digits);

            // Remove any trailing zeros
            while result.digits.len() > 1 && *result.digits.last().unwrap() == 0 {
                result.digits.pop();
            }

            if result.is_zero() {
                result.negative = false;
            } else {
                result.negative = negative;
            }

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

    fn is_zero(&self) -> bool {
        self.digits.len() == 1 && self.digits[0] == 0
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
