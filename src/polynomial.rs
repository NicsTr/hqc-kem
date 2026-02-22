use core::ops::{Add, Div, Mul, Sub};

use hybrid_array::{
    Array, ArraySize,
    sizes::{U1, U64},
    typenum::{Diff, Quot, Sum, Unsigned},
};
use zerocopy::IntoBytes;

/// Packed binary polynomial
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BinaryPolynomial<NBits>(Array<u64, Sum<Quot<Diff<NBits, U1>, U64>, U1>>)
where
    NBits: Sub<U1> + Unsigned,
    Diff<NBits, U1>: Div<U64>,
    Quot<Diff<NBits, U1>, U64>: Add<U1>,
    Sum<Quot<Diff<NBits, U1>, U64>, U1>: ArraySize;

impl<NBits> BinaryPolynomial<NBits>
where
    NBits: Sub<U1> + Unsigned,
    Diff<NBits, U1>: Div<U64>,
    Quot<Diff<NBits, U1>, U64>: Add<U1>,
    Sum<Quot<Diff<NBits, U1>, U64>, U1>: ArraySize,
{
    pub(crate) fn zero() -> Self {
        Array::default().into()
    }

    /// Set coefficient at index `index` to 1. The caller
    /// is responsible for keeping index in bound, else it will cause a panic.
    pub(crate) fn set_coefficient(&mut self, index: usize) {
        self.0[index / 64] |= 1 << (index % 64);
    }

    /// Return a reference to a slice of exactly `NBytes` bytes into this polynomial.
    ///
    /// This should avoid any copy.
    pub(crate) fn as_bytes_truncated<NBytes: ArraySize + Unsigned>(&self) -> &[u8] {
        const { assert!(NBytes::USIZE * 8 < NBits::USIZE) }
        &self.0.as_bytes()[..NBytes::USIZE]
    }
}

impl<NBits> From<Array<u64, Sum<Quot<Diff<NBits, U1>, U64>, U1>>> for BinaryPolynomial<NBits>
where
    NBits: Sub<U1> + Unsigned,
    Diff<NBits, U1>: Div<U64>,
    Quot<Diff<NBits, U1>, U64>: Add<U1>,
    Sum<Quot<Diff<NBits, U1>, U64>, U1>: ArraySize,
{
    fn from(value: Array<u64, Sum<Quot<Diff<NBits, U1>, U64>, U1>>) -> Self {
        BinaryPolynomial(value)
    }
}

impl<NBits> From<BinaryPolynomial<NBits>> for Array<u64, Sum<Quot<Diff<NBits, U1>, U64>, U1>>
where
    NBits: Sub<U1> + Unsigned,
    Diff<NBits, U1>: Div<U64>,
    Quot<Diff<NBits, U1>, U64>: Add<U1>,
    Sum<Quot<Diff<NBits, U1>, U64>, U1>: ArraySize,
{
    fn from(value: BinaryPolynomial<NBits>) -> Self {
        value.0
    }
}

impl<NBits> Add for BinaryPolynomial<NBits>
where
    NBits: Sub<U1> + Unsigned,
    Diff<NBits, U1>: Div<U64>,
    Quot<Diff<NBits, U1>, U64>: Add<U1>,
    Sum<Quot<Diff<NBits, U1>, U64>, U1>: ArraySize,
{
    type Output = BinaryPolynomial<NBits>;

    fn add(self, rhs: Self) -> Self::Output {
        BinaryPolynomial(rhs.0.iter().zip(self.0).map(|(a, b)| a ^ b).collect())
    }
}

impl<NBits> Mul<&Self> for BinaryPolynomial<NBits>
where
    NBits: Sub<U1> + Unsigned,
    Diff<NBits, U1>: Div<U64>,
    Quot<Diff<NBits, U1>, U64>: Add<U1>,
    Sum<Quot<Diff<NBits, U1>, U64>, U1>: ArraySize,
{
    type Output = BinaryPolynomial<NBits>;

    /// Highly inneficient and naive constant-time multiplication of binary polynomial
    /// modulo X^N - 1.
    ///
    // TODO: This bitwise schoolbook multiplication should be optimized using
    // fancy Karatsuba + Toom-Cook multiplication and architeecture dependent opitmizations
    // (like pcmul or RISC-V's Zbc extension) as suggested by HQC specification.
    fn mul(self, rhs: &Self) -> Self::Output {
        let mut res = Array::default();
        for i in 0..NBits::USIZE {
            let ai = (self.0[i / 64] >> (i % 64)) & 1;
            for j in 0..NBits::USIZE {
                let bj = (rhs.0[j / 64] >> (j % 64)) & 1;
                let target_index = (i + j) % NBits::USIZE;
                res[target_index / 64] ^= (ai & bj) << (target_index % 64);
            }
        }
        res.into()
    }
}

#[cfg(test)]
mod test {
    use crate::{polynomial::BinaryPolynomial, utils::XofState};
    use hybrid_array::{
        Array,
        sizes::{U2, U5, U127, U1040, U2048},
    };

    #[test]
    fn test_truncation() {
        let polynomial: BinaryPolynomial<U127> = BinaryPolynomial(Array::<u64, U2>([
            0x0706_0504_0302_0100,
            0x0F0E_0D0C_0B0A_0908,
        ]));

        assert_eq!(polynomial.as_bytes_truncated::<U5>(), [0, 1, 2, 3, 4]);
    }

    #[test]
    fn test_polynomial_size() {
        let _: BinaryPolynomial<U1040> = Array([0u64; 17]).into();
        let _: BinaryPolynomial<U2048> = Array([0u64; 32]).into();
    }

    #[test]
    fn test_add_polynomial() {
        let mut xof = XofState::new(&[13, 37]);

        for _ in 0..100 {
            let a = xof.sample_vect::<U1040>();
            let b = xof.sample_vect::<_>();
            assert_eq!(a.clone() + a.clone(), BinaryPolynomial::zero());
            let c = a.clone() + b.clone();

            for (i, v) in c.0.iter().enumerate() {
                assert_eq!(*v, a.0[i] ^ b.0[i]);
            }
        }
    }

    #[test]
    fn test_mul_polynomial() {
        let mut xof = XofState::new(&[13, 38]);

        let tmp: BinaryPolynomial<U127> = BinaryPolynomial(Array::<u64, U2>([
            0xaaaa_bbbb_cccc_dddd,
            0x9999_8888_7777_6666,
        ])) * &Array([0xbc, 0x6f]).into();

        assert_eq!(
            tmp,
            Array([0xfff9_bbc1_fff9_bb86, 0x333e_dda7_eee3_0055]).into()
        );

        // Test distributivity with addition.
        for _ in 0..10 {
            let a = xof.sample_vect::<U1040>();
            let b = xof.sample_vect::<_>();
            let c = xof.sample_vect::<_>();

            assert_eq!(
                a.clone() * &BinaryPolynomial::zero(),
                BinaryPolynomial::zero()
            );
            assert_eq!(
                c.clone() * &(a.clone() + b.clone()),
                c.clone() * &a + c * &b
            );
        }
    }
}
