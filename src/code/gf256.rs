use core::fmt::Debug;
use core::ops::{Add, AddAssign, Mul, MulAssign};

use ctutils::{Choice, CtAssign, CtEq, CtGt, CtSelect};

use crate::code::reed_solomon::CtEqZero;

#[derive(Clone, Copy, PartialEq, Eq, Default)]
#[repr(transparent)]
pub(crate) struct Gf256(pub u8);

const MODULE: u8 = 0b0001_1101;

impl Gf256 {
    /// Constant time multiplication by X.
    fn mul_x(self) -> Self {
        let do_reduce = self.0.ct_gt(&127);

        Gf256((self.0 << 1) ^ 0.ct_select(&MODULE, do_reduce))
    }

    /// Constant time square-and-multiply exponentiation.
    pub(crate) fn pow(self, exp: u8) -> Self {
        let mut res = Gf256(1);
        for i in 0..u8::BITS {
            // Square
            res *= res;
            // Constant-time conditional multiply
            let do_multiply = Choice::from_u8_lsb((exp >> (u8::BITS - i - 1)) & 1);
            res *= Gf256(1.ct_select(&self.0, do_multiply));
        }

        res
    }

    /// Constant time inversion in the field.
    ///
    /// For completeness, inv(0) = 0.
    // TODO: optimize with inline square and multiply
    pub(crate) fn inv(self) -> Self {
        self.pow(254)
    }
}

impl Debug for Gf256 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:02x}", &self.0)
    }
}

impl From<u8> for Gf256 {
    fn from(value: u8) -> Self {
        Gf256(value)
    }
}

impl From<Gf256> for u8 {
    fn from(value: Gf256) -> Self {
        value.0
    }
}

impl Add<Self> for Gf256 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl AddAssign for Gf256 {
    fn add_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0
    }
}

impl Mul<Self> for Gf256 {
    type Output = Self;

    /// Constant time double-and-add multiplication.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut res = Gf256(0);
        for i in 0..u8::BITS {
            // Double
            res = res.mul_x();
            // Conditional add
            let do_add = Choice::from_u8_lsb((self.0 >> (u8::BITS - i - 1)) & 1);
            res += Gf256(0.ct_select(&rhs.0, do_add));
        }
        res
    }
    // TODO: LOG_TABLE implem for time-memory trade-off?
}

impl MulAssign for Gf256 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl CtEq for Gf256 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl CtSelect for Gf256 {
    fn ct_select(&self, other: &Self, choice: Choice) -> Self {
        Gf256(u8::ct_select(&self.0, &other.0, choice))
    }
}

impl CtEqZero for Gf256 {
    fn ct_eq_zero(&self) -> Choice {
        self.0.ct_eq_zero()
    }
}

impl CtAssign for Gf256 {
    fn ct_assign(&mut self, other: &Gf256, choice: Choice) {
        self.0.ct_assign(&other.0, choice);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_mul_x() {
        for i in 0..127 {
            assert_eq!(Gf256(i).mul_x(), Gf256(2 * i));
        }

        for i in 128..=255 {
            assert_eq!(Gf256(i).mul_x(), Gf256(i.wrapping_mul(2)) + Gf256(MODULE));
        }
    }

    #[test]
    fn test_inv() {
        assert_eq!(Gf256(0).inv(), Gf256(0));

        for a in 1..=255 {
            assert_eq!(Gf256(a) * Gf256(a).inv(), Gf256(1), "a: {a}");
        }
    }

    #[test]
    fn test_mul() {
        for a in 0..=255 {
            let a = Gf256(a);
            for i in 0..=255 {
                let prod = a * Gf256(i);
                if a.0 == 0 || i == 0 {
                    assert_eq!(prod * a.inv(), Gf256(0),);
                    assert_eq!(prod * a.inv(), Gf256(0),);
                } else {
                    assert_eq!(prod * a.inv(), Gf256(i),);
                    assert_eq!(prod * a.inv(), Gf256(i),);
                }
            }
        }
    }

    #[test]
    fn test_pow() {
        for exp in 1..=254 {
            assert_eq!(Gf256(0).pow(exp), Gf256(0));
            assert_eq!(Gf256(1).pow(exp), Gf256(1));

            for a in 2..=255 {
                let a = Gf256(a);
                let mut res = Gf256(1);
                for _ in 0..exp {
                    res *= a;
                }
                assert_eq!(a.pow(exp), res);
            }
        }
    }

    #[test]
    fn test_multiplicative_order() {
        let a = Gf256(2);
        let mut c = 1usize;

        while a.pow(c as u8) != Gf256(1) && c < 256 {
            c += 1;
        }
        assert_eq!(c, 255);
    }
}
