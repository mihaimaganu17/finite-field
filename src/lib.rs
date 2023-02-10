#![feature(step_trait)]

use core::{
    fmt::{self, Debug, Display},
    ops::{Add, Mul, Div, Rem, Sub, BitAnd, Shr},
};
use primitive_types::{U256, U512};

pub trait Element:
    Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + BitAnd<Output = Self>
    + Shr<Output = Self>
    + PartialEq
    + PartialOrd
    + Sized
    + Debug
    + Display
    + Copy
    + Clone
    + TryInto<i64>
{
    const ADDITIVE_IDENTITY: Self;
    const MULTIPLICATION_IDENTITY: Self;
    // TODO! Add docs for this
    // TODO! Add macro for this
    fn add_mod(self, other: Self, modulo: Self) -> Self;
    // Function which multiplies `self` with `other` by upcasting the type to a representation of
    // double of bits, modulo it and then downcasting it again.
    //
    // TODO! Write a macro for this
    fn mul_mod(self, other: Self, modulo: Self) -> Self;
}

impl Element for u8 {
    const ADDITIVE_IDENTITY: u8 = 0u8;
    const MULTIPLICATION_IDENTITY: u8 = 1u8;
    fn add_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as u16;
        let right = other as u16;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left + right) % modulo as u16) as u8;
        result
    }
    fn mul_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as u16;
        let right = other as u16;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left * right) % modulo as u16) as u8;
        result
    }
}

impl Element for u16 {
    const ADDITIVE_IDENTITY: u16 = 0u16;
    const MULTIPLICATION_IDENTITY: u16 = 1u16;
    fn add_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as u32;
        let right = other as u32;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left + right) % modulo as u32) as u16;
        result
    }
    fn mul_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as u32;
        let right = other as u32;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left * right) % modulo as u32) as u16;
        result
    }
}

impl Element for u32 {
    const ADDITIVE_IDENTITY: u32 = 0u32;
    const MULTIPLICATION_IDENTITY: u32 = 1u32;
    fn add_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as u64;
        let right = other as u64;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left + right) % modulo as u64) as u32;
        result
    }
    fn mul_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as u64;
        let right = other as u64;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left * right) % modulo as u64) as u32;
        result
    }
}

impl Element for i32 {
    const ADDITIVE_IDENTITY: i32 = 0i32;
    const MULTIPLICATION_IDENTITY: i32 = 1i32;
    fn add_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as i64;
        let right = other as i64;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left + right) % modulo as i64) as i32;
        result
    }
    fn mul_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as i64;
        let right = other as i64;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left * right) % modulo as i64) as i32;
        result
    }
}

impl Element for u64 {
    const ADDITIVE_IDENTITY: u64 = 0u64;
    const MULTIPLICATION_IDENTITY: u64 = 1u64;
    fn add_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as u128;
        let right = other as u128;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left + right) % modulo as u128) as u64;
        result
    }
    fn mul_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as u128;
        let right = other as u128;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left * right) % modulo as u128) as u64;
        result
    }
}

impl Element for i64 {
    const ADDITIVE_IDENTITY: i64 = 0i64;
    const MULTIPLICATION_IDENTITY: i64 = 1i64;
    fn add_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as i128;
        let right = other as i128;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left + right) % modulo as i128) as i64;
        result
    }
    fn mul_mod(self, other: Self, modulo: Self) -> Self {
        let left = self as i128;
        let right = other as i128;
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it againa to the original type
        let result = ((left * right) % modulo as i128) as i64;
        result
    }
}

impl Element for U256 {
    const ADDITIVE_IDENTITY: U256 = U256::zero();
    const MULTIPLICATION_IDENTITY: U256 = U256::one();
    fn add_mod(self, other: Self, modulo: Self) -> Self {
        // Since we modulo the result with a type that cannot exceed the MAX value of the type,
        // it is safe to downcast it again to the original type
        let result = U256::try_from((U512::from(self) + U512::from(other)) % U512::from(modulo))
            .unwrap();
        result
    }
    fn mul_mod(self, other: Self, modulo: Self) -> Self {
        let result = U256::try_from(self.full_mul(other) % U512::from(modulo))
            .unwrap();
        result
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FieldElement<T: Element> {
    pub value: T,
    pub order: T,
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

    pub fn pow(self, exponent: T) -> Result<Self, FieldElementError> {
        // If the exponent is zero, we always return the multiplication identity, which is
        // basically 1 every time
        if exponent == T::ADDITIVE_IDENTITY {
            return Ok(Self {
                value: T::MULTIPLICATION_IDENTITY,
                order: self.order,
            });
        }


        // Initialize the operation exponent as the initial exponent at first
        let mut positive_exponent = exponent;

        // If the exponent is a negative value, we just replace it with its complement in the
        // finite field which is always positive
        if positive_exponent < T::ADDITIVE_IDENTITY {
            positive_exponent = (positive_exponent % self.order) + (self.order
                - T::MULTIPLICATION_IDENTITY);
        }

        // We perform the operation as a series of multiplication steps, applying modulo every time
        // such that we make the function work less
        let mut local_exponent = positive_exponent;
        let mut cache_value = self.value;
        let mut value = T::MULTIPLICATION_IDENTITY;

        while local_exponent != T::ADDITIVE_IDENTITY {
            if local_exponent & T::MULTIPLICATION_IDENTITY == T::MULTIPLICATION_IDENTITY {
                value = value.mul_mod(cache_value, self.order);
            }
            local_exponent = local_exponent >> T::MULTIPLICATION_IDENTITY;
            cache_value = cache_value.mul_mod(cache_value, self.order);
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

impl<T: Element> Mul<T> for FieldElement<T> {
    type Output = Self;

    fn mul(self, other: T) -> Self::Output {
        let value = self.value.mul_mod(other, self.order);

        Self {
            value,
            order: self.order,
        }
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

        let value = self.value.add_mod(other.value, self.order);

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
        let value = self.value.add_mod(other_complement, self.order);

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
        let value = self.value.mul_mod(other.value, self.order);

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

        let other = other.pow(
            self.order - T::MULTIPLICATION_IDENTITY - T::MULTIPLICATION_IDENTITY
        ).unwrap();

        let value = self.value.mul_mod(other.value, self.order);

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
