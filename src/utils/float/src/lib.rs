#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn show_float_test() {
        let float = Float::from(114.514);
        let s = format!("{}", float);
        assert_eq!(s, "114.514");
    }

    #[test]
    fn float_eq_test() {
        let a = Float::from(114.514);
        let b  = Float::from(114.514);
        assert_eq!(a, b);
    }

    #[test]
    fn float_neq_test() {
        let a = Float::from(114.514);
        let b  = Float::from(1919.810);
        assert_ne!(a, b);
    }
}

use std::fmt::{Display, Formatter};
use std::ops::{Add, Mul, Div};

#[derive(Debug, Copy, Clone)]
pub struct Float {
    value: f32
}

impl Display for Float {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Add for Float {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Float::from(self.value + rhs.value)
    }
}

impl Mul for Float {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Float::from(self.value * rhs.value)
    }
}

impl Div for Float {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Float::from(self.value / rhs.value)
    }
}

impl PartialEq for Float {
    fn eq(&self, other: &Self) -> bool {
        float_eq(self.value, other.value, 0.0001)
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

fn float_eq(a: f32, b: f32, det: f32) -> bool {
    let real_det = (a - b).abs();
    real_det < det
}

impl From<String> for Float {
    fn from(value: String) -> Self {
        Float::from(value.parse::<f32>().unwrap())
    }
}


impl From<f32> for Float {
    fn from(value: f32) -> Self {
        Float { value }
    }
}

impl Into<String> for Float {
    fn into(self) -> String {
        format!("{}", self.value)
    }
}

impl Into<f32> for Float {
    fn into(self) -> f32 {
        self.value
    }
}