#![feature(step_trait)]

use core::{
    fmt::{self, Debug, Display},
    ops::{Add, Mul, Div, Rem, Sub},
};

pub trait Element:
    Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + PartialEq
    + PartialOrd
    + Sized
    + Debug
    + Display
    + Copy
    + Clone
    + TryInto<i64>
    + std::iter::Step
{
    const ADDITIVE_IDENTITY: Self;
    const MULTIPLICATION_IDENTITY: Self;
}

impl Element for u8 {
    const ADDITIVE_IDENTITY: u8 = 0u8;
    const MULTIPLICATION_IDENTITY: u8 = 1u8;
}

impl Element for u16 {
    const ADDITIVE_IDENTITY: u16 = 0u16;
    const MULTIPLICATION_IDENTITY: u16 = 1u16;
}

impl Element for u32 {
    const ADDITIVE_IDENTITY: u32 = 0u32;
    const MULTIPLICATION_IDENTITY: u32 = 1u32;
}

impl Element for u64 {
    const ADDITIVE_IDENTITY: u64 = 0u64;
    const MULTIPLICATION_IDENTITY: u64 = 1u64;
}

#[derive(Debug, Clone, Copy)]
struct FieldElement<T: Element> {
    value: T,
    order: T,
}

impl<T: Element> FieldElement<T> {
    /// Creates a new `FieldElement` or `order` and with the passed `value`
    pub fn new(value: T, order: T) -> Result<Self, FieldElementError> {
        let value = value % order;
        if value >= order || value < T::ADDITIVE_IDENTITY {
            return Err(FieldElementError::ValueNotWithinBounds);
        }

        Ok(Self { value, order })
    }

    pub fn pow(self, exponent: i64) -> Result<Self, FieldElementError> {
        // If the exponent is zero, we always return the multiplication identity, which is
        // basically 1 every time
        if exponent == 0 {
            return Ok(Self {
                value: T::MULTIPLICATION_IDENTITY,
                order: self.order,
            });
        }

        // Initialize the base value of the operation
        let mut value = self.value;

        // Initialize the operation exponent as the initial exponent at first
        let mut positive_exponent = exponent;

        // Convert the order of the current element to an actual numerical type, such that we can
        // perform operations with it and the exponent passed to this function
        let numeric_order: i64 = match self.order.try_into() {
            Ok(order) => order,
            Err(_err) => { return Err(FieldElementError::FailedConvertionToI16); }
        };


        // If the exponent is a negative value, we just replace it with its complement in the
        // finite field which is always positive
        if positive_exponent < 0 {
            positive_exponent = (positive_exponent % numeric_order) + (numeric_order - 1);
        }

        // We perform the operation as a series of multiplication steps, applying modulo every time
        // such that we make the function work less
        for _ in 1..positive_exponent {
            value = (value * self.value) % self.order;
        }

        // Return the result
        Ok(Self {
            value,
            order: self.order,
        })
    }
}

impl<T: Element> PartialEq for FieldElement<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.order == other.order
    }
}

impl<T: Element> Add for FieldElement<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        if self.order != other.order {
            panic!(
                "Mismatching finite fields order: {:?} != {:?}",
                self.order, other.order
            );
        }

        let value = (self.value + other.value) % self.order;

        Self {
            value,
            order: self.order,
        }
    }
}

impl<T: Element> Sub for FieldElement<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        if self.order != other.order {
            panic!(
                "Mismatching finite fields order: {:?} != {:?}",
                self.order, other.order
            );
        }

        // Compute the complement of the substracted element. By doing this we make sure that we do
        // not obtain negative values which will be harder to deal after the substraction operation
        //
        // We also know for a fact that `value` is always smaller than `order` so the
        // subtraction is safe.
        let other_complement = other.order - other.value;

        // The subtraction operation itself becomes an addition with the complement
        let value = (self.value + other_complement) % self.order;

        Self {
            value,
            order: self.order,
        }
    }
}

impl<T: Element> Mul for FieldElement<T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        if self.order != other.order {
            panic!(
                "Mismatching finite fields order: {:?} != {:?}",
                self.order, other.order
            );
        }

        // The subtraction operation itself becomes an addition with the complement
        let value = (self.value * other.value) % self.order;

        Self {
            value,
            order: self.order,
        }
    }
}

impl<T: Element> Div for FieldElement<T> {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        if self.order != other.order {
            panic!(
                "Mismatching finite fields order: {:?} != {:?}",
                self.order, other.order
            );
        }

        let other = other.pow(-1).unwrap();

        let value = (self.value * other.value) % self.order;

        Self {
            value,
            order: self.order,
        }
    }
}

impl<T: Element> fmt::Display for FieldElement<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}({})", self.value, self.order)
    }
}


#[derive(Debug)]
pub enum FieldElementError {
    ValueNotWithinBounds,
    FailedConvertionToI16,
}

#[cfg(test)]
mod tests {
    use crate::FieldElement;

    #[test]
    fn test_ne() {
        let a = FieldElement::<u32>::new(2, 31).unwrap();
        let b = FieldElement::<u32>::new(2, 31).unwrap();
        let c = FieldElement::<u32>::new(15, 31).unwrap();

        assert_eq!(a, b);
        assert!(a != c);
        assert!(a == b);
    }

    #[test]
    fn test_add() {
        let a = FieldElement::<u32>::new(2, 31).unwrap();
        let b = FieldElement::<u32>::new(15, 31).unwrap();
        assert_eq!(a + b, FieldElement::<u32>::new(17, 31).unwrap());

        let a = FieldElement::<u32>::new(17, 31).unwrap();
        let b = FieldElement::<u32>::new(21, 31).unwrap();
        assert_eq!(a + b, FieldElement::<u32>::new(7, 31).unwrap());
    }

    #[test]
    fn test_sub() {
        let a = FieldElement::<u32>::new(29, 31).unwrap();
        let b = FieldElement::<u32>::new(4, 31).unwrap();
        assert_eq!(a - b, FieldElement::<u32>::new(25, 31).unwrap());

        let a = FieldElement::<u32>::new(15, 31).unwrap();
        let b = FieldElement::<u32>::new(30, 31).unwrap();
        assert_eq!(a - b, FieldElement::<u32>::new(16, 31).unwrap());
    }

    #[test]
    fn test_mul() {
        let a = FieldElement::<u32>::new(24, 31).unwrap();
        let b = FieldElement::<u32>::new(19, 31).unwrap();
        assert_eq!(a * b, FieldElement::<u32>::new(22, 31).unwrap());
    }

    #[test]
    fn test_pow() {
        let a = FieldElement::<u32>::new(17, 31).unwrap();
        assert_eq!(a.pow(3).unwrap(), FieldElement::<u32>::new(15, 31).unwrap());

        let a = FieldElement::<u32>::new(5, 31).unwrap();
        let b = FieldElement::<u32>::new(18, 31).unwrap();
        assert_eq!(a.pow(5).unwrap() * b, FieldElement::<u32>::new(16, 31).unwrap());
    }

    #[test]
    fn exercise4() {
        let k_value: [u64; 5] = [1, 3, 7, 13, 18];

        for k in k_value {
            let k = FieldElement::<u64>::new(k, 19).unwrap();
            let mut finite_field = vec![];
            for element in 0..19 {
                let elem = FieldElement::<u64>::new(element, 19).unwrap();
                finite_field.push(elem * k);
            }
            println!("Finite fields for k = {} is {}", k,
                finite_field.iter().fold(String::from(""), |acc, x| format!("{}, {}", acc, x)));
        }
    }

    #[test]
    fn exercise7() {
        let p_value: [u64; 4] = [7, 11, 17, 31];

        for p in p_value {
            let mut finite_field = vec![];
            for element in 1..p {
                let elem = FieldElement::<u64>::new(element, p).unwrap();
                finite_field.push(elem.pow((p-1) as i64).unwrap());
            }

            println!("Finite fields for k = {} is {}", p,
                finite_field.iter().fold(String::from(""), |acc, x| format!("{}, {}", acc, x)));
        }
    }

    #[test]
    fn exercise8() {
        let a = FieldElement::<u64>::new(3, 31).unwrap();
        let b = FieldElement::<u64>::new(24, 31).unwrap();
        let c = FieldElement::<u64>::new(4, 31).unwrap();
        assert_eq!(a / b, c);

        let a = FieldElement::<u64>::new(17, 31).unwrap();
        let b = FieldElement::<u64>::new(29, 31).unwrap();
        assert_eq!(a.pow(-3).unwrap(), b);

        let a = FieldElement::<u64>::new(4, 31).unwrap();
        let b = FieldElement::<u64>::new(11, 31).unwrap();
        let c = FieldElement::<u64>::new(13, 31).unwrap();
        assert_eq!(a.pow(-4).unwrap() * b, c);
    }
}
