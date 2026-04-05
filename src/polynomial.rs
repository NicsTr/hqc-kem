use core::ops::{Add, Mul};

use ctutils::CtEq;
use hybrid_array::{
    Array, ArraySize,
    sizes::{U2, U8, U64},
    typenum::{Prod, Unsigned},
};

use zerocopy::IntoBytes;

use crate::size_traits::{Bytesize, Octobytesize, WordsizeFromBitsize};

/// Packed binary polynomial
#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct BinaryPolynomial<NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>>(
    Array<u64, Octobytesize<NBits>>,
)
where
    Octobytesize<NBits>: Mul<U2>,
    Prod<Octobytesize<NBits>, U2>: ArraySize;

impl<NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>> BinaryPolynomial<NBits>
where
    Octobytesize<NBits>: Mul<U2>,
    Prod<Octobytesize<NBits>, U2>: ArraySize,
{
    const LAST_WORD_SHIFT: u32 = ((NBits::U32 - 1) % u64::BITS) + 1u32;

    const LAST_WORD_MASK: u64 = (1u64.unbounded_shl(Self::LAST_WORD_SHIFT)).wrapping_sub(1);

    pub(crate) fn zero() -> Self {
        Array::default().into()
    }

    /// Set coefficient at index `index` to 1. The caller
    /// is responsible for keeping index in bound, else it will cause a panic.
    pub(crate) fn set_coefficient(&mut self, index: usize) {
        self.0[index / 64] |= 1 << (index % 64);
    }

    /// Return a mutable reference to a slice of exactly `NBytes` bytes into this polynomial.
    ///
    /// This should avoid any copy.
    pub(crate) fn as_mut_bytes_truncated<NBytes: ArraySize>(&mut self) -> &mut [u8] {
        const { assert!(NBytes::USIZE * 8 < NBits::USIZE) }
        &mut self.0.as_mut_bytes()[..NBytes::USIZE]
    }

    /// Return a reference to a slice of exactly `NBytes` bytes into this polynomial.
    ///
    /// This should avoid any copy.
    pub(crate) fn as_bytes_truncated<NBytes: ArraySize>(&self) -> &[u8] {
        const { assert!(NBytes::USIZE * 8 < NBits::USIZE) }
        &self.0.as_bytes()[..NBytes::USIZE]
    }

    /// Reduction modulo X^NBits - 1
    fn reduce(mut value: Array<u64, Prod<Octobytesize<NBits>, U2>>) -> Self {
        let reduced_size = Octobytesize::<NBits>::USIZE;

        for i in 0..reduced_size {
            value[i] ^= value[reduced_size + i - 1].unbounded_shr(Self::LAST_WORD_SHIFT)
                ^ (value[reduced_size + i].unbounded_shl(u64::BITS - Self::LAST_WORD_SHIFT))
        }
        value[reduced_size - 1] &= Self::LAST_WORD_MASK;

        Self(value[..reduced_size].try_into().unwrap())
    }

    /// Karatsuba multiplication using only 2n temporary buffer
    ///
    /// Both paramaters are mutated while computing, but restored before returning.
    pub(crate) fn low_stack_mul(&mut self, other: &mut Self) -> Self {
        let mut tmp = Array::<u64, Prod<Octobytesize<NBits>, U2>>::default();

        karatsuba_multiplication::cumulative_karatsuba(&mut tmp[..], &mut self.0, &mut other.0);
        Self::reduce(tmp)
    }

    // cumulative_karatsuba_inner(&mut self,
}

mod karatsuba_multiplication {

    /// Base cumulative multiplication.
    fn base_mul(c: &mut [u64; 2], a: u64, b: u64) {
        for i in 0..u64::BITS {
            let ai = (a >> i) & 1;
            for j in 0..u64::BITS {
                let bj = (b >> j) & 1;
                let target_index = (i + j) as usize;
                c[target_index / (u64::BITS as usize)] ^=
                    (ai & bj) << (target_index % (u64::BITS as usize));
            }
        }
    }

    /// Xor part of `value` to itself (may overlap).
    #[inline]
    fn overlapping_xor(value: &mut [u64], offset_dst: usize, offset_src: usize, length: usize) {
        if offset_dst <= offset_src {
            for i in 0..length {
                value[offset_dst + i] ^= value[offset_src + i];
            }
        } else {
            for i in (0..length).rev() {
                value[offset_dst + i] ^= value[offset_src + i];
            }
        }
    }

    /// Xor `a` into `b`.
    #[inline]
    fn xor(b: &mut [u64], a: &[u64]) {
        for (bi, ai) in b.iter_mut().zip(a) {
            *bi ^= ai;
        }
    }

    /// In-place cumulative Karatsuba multiplication, computing `c += a*b`
    ///
    /// From Grenet 2025
    ///
    /// `a` and `b` must be of same size.
    /// `c` must be two times bigger than `a` (and `b`). `a` and `b` will be temporarily
    /// modified durign the computation, but will be restored before returning.
    pub(super) fn cumulative_karatsuba(c: &mut [u64], a: &mut [u64], b: &mut [u64]) {
        debug_assert_eq!(a.len(), b.len());
        debug_assert_eq!(c.len(), a.len() + b.len());

        if a.len() == 1 {
            base_mul(c.try_into().unwrap(), a[0], b[0]);
            return;
        }

        let split = a.len().div_ceil(2);
        let c_len = c.len();

        overlapping_xor(c, split, 0, split);
        overlapping_xor(c, 2 * split, split, split);
        overlapping_xor(c, 3 * split, 2 * split, c_len - 3 * split);

        let (a0, a1) = a.split_at_mut(split);
        let (b0, b1) = b.split_at_mut(split);

        cumulative_karatsuba(&mut c[..a0.len() + b0.len()], a0, b0);
        cumulative_karatsuba(&mut c[split..split + a1.len() + b1.len()], a1, b1);

        overlapping_xor(c, 3 * split, 2 * split, c_len - 3 * split);
        overlapping_xor(c, 2 * split, split, split);
        overlapping_xor(c, split, 0, split);

        xor(a0, a1);
        xor(b0, b1);

        cumulative_karatsuba(&mut c[split..split + a0.len() + b0.len()], a0, b0);

        xor(a0, a1);
        xor(b0, b1);
    }
}

impl<NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>> From<&Array<u8, Bytesize<NBits>>>
    for BinaryPolynomial<NBits>
where
    Octobytesize<NBits>: Mul<U2>,
    Prod<Octobytesize<NBits>, U2>: ArraySize,
{
    fn from(value: &Array<u8, Bytesize<NBits>>) -> Self {
        const {
            assert!(Bytesize::<NBits>::USIZE <= 8 * Octobytesize::<NBits>::USIZE);
            assert!(Bytesize::<NBits>::USIZE > 8 * (Octobytesize::<NBits>::USIZE - 1));
        }

        let mut res = Array::default();
        let mut chunk_iter = value.chunks_exact(size_of::<u64>());
        for (a, b) in res.iter_mut().zip(&mut chunk_iter) {
            // Cannot fail with the use of chunks_exact
            *a = u64::from_le_bytes(b.try_into().unwrap());
        }

        let remainder = chunk_iter.remainder();
        let mut last_word = [0u8; size_of::<u64>()];
        // Cannot fail since remainder length is guaranteed to be strictly less than size_of::<u64>
        last_word[..remainder.len()].copy_from_slice(remainder);

        // Cannot fail since res is never empty
        *res.last_mut().unwrap() = u64::from_le_bytes(last_word) & Self::LAST_WORD_MASK;

        Self(res)
    }
}

impl<NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>> From<&BinaryPolynomial<NBits>>
    for Array<u8, Bytesize<NBits>>
where
    Octobytesize<NBits>: Mul<U2>,
    Prod<Octobytesize<NBits>, U2>: ArraySize,
{
    fn from(value: &BinaryPolynomial<NBits>) -> Self {
        const {
            assert!(Bytesize::<NBits>::USIZE <= 8 * Octobytesize::<NBits>::USIZE);
            assert!(Bytesize::<NBits>::USIZE > 8 * (Octobytesize::<NBits>::USIZE - 1));
            assert!(size_of::<BinaryPolynomial<NBits>>() != 0)
        }

        let mut res = Array::default();
        let mut chunk_iter = res.chunks_exact_mut(size_of::<u64>());
        for (a, b) in (&mut chunk_iter).zip(value.0.iter()) {
            // Cannot fail since chunk is of exactly the right size
            a.copy_from_slice(&b.to_le_bytes());
        }

        let remainder = chunk_iter.into_remainder();

        // Cannot fail since value is never empty and slice sizes are equals
        remainder.copy_from_slice(&value.0.last().unwrap().to_le_bytes()[..remainder.len()]);

        res
    }
}

impl<NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>>
    From<Array<u64, Octobytesize<NBits>>> for BinaryPolynomial<NBits>
where
    Octobytesize<NBits>: Mul<U2>,
    Prod<Octobytesize<NBits>, U2>: ArraySize,
{
    fn from(mut value: Array<u64, Octobytesize<NBits>>) -> Self {
        // Never panics: NBits is NonZero
        *value.last_mut().unwrap() &= BinaryPolynomial::<NBits>::LAST_WORD_MASK;
        BinaryPolynomial(value)
    }
}

impl<NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>> Add for BinaryPolynomial<NBits>
where
    Octobytesize<NBits>: Mul<U2>,
    Prod<Octobytesize<NBits>, U2>: ArraySize,
{
    type Output = BinaryPolynomial<NBits>;

    fn add(self, rhs: Self) -> Self::Output {
        BinaryPolynomial(rhs.0.iter().zip(self.0).map(|(a, b)| a ^ b).collect())
    }
}

impl<NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>> CtEq for BinaryPolynomial<NBits>
where
    Octobytesize<NBits>: Mul<U2>,
    Prod<Octobytesize<NBits>, U2>: ArraySize,
{
    fn ct_eq(&self, other: &Self) -> ctutils::Choice {
        self.0.ct_eq(&other.0)
    }
}

#[cfg(test)]
mod test {
    use core::ops::Mul;

    use crate::pke::PkeParams;
    use crate::polynomial::karatsuba_multiplication;
    use crate::size_traits::{Octobytesize, WordsizeFromBitsize};
    use crate::{Hqc1, Hqc3, Hqc5};
    use crate::{hash::XofState, polynomial::BinaryPolynomial};
    use hybrid_array::ArraySize;
    use hybrid_array::typenum::Prod;
    use hybrid_array::{
        Array,
        sizes::{U2, U3, U4, U5, U8, U64, U127, U175, U256, U1040, U2048},
    };
    use rand::rngs::StdRng;
    use rand::{RngExt, SeedableRng};

    impl<NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>> Mul<&Self>
        for BinaryPolynomial<NBits>
    where
        Octobytesize<NBits>: Mul<U2>,
        Prod<Octobytesize<NBits>, U2>: ArraySize,
    {
        type Output = BinaryPolynomial<NBits>;

        /// Highly inneficient and naive constant-time multiplication of binary polynomial
        /// modulo X^N - 1.
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
            let a = xof.sample_vect::<Hqc1>();
            let b = xof.sample_vect::<Hqc1>();
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
            0x1999_8888_7777_6666,
        ])) * &Array([0xbc, 0x6f]).into();

        assert_eq!(
            tmp,
            Array([0xfff9_bbc1_fff9_bb86, 0x333e_dda7_eee3_0055]).into()
        );

        // Test distributivity with addition.
        for _ in 0..10 {
            let a = xof.sample_vect::<Hqc1>();
            let b = xof.sample_vect::<Hqc1>();
            let c = xof.sample_vect::<Hqc1>();

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

    #[test]
    fn test_low_stack_mult_basic() {
        let a = [0xaaaa_bbbb_cccc_dddd, 0x1999_8888_7777_6666, 0, 0];
        let b = [0x0706_0504_0302_0100, 0x0F0E_0D0C_0B0A_0908, 0, 0];

        let c: BinaryPolynomial<U256> =
            BinaryPolynomial(Array(a)).low_stack_mul(&mut BinaryPolynomial(Array(b)));
        // BinaryPolynomial::<U127>::low_stack_mult(&mut BinaryPolynomial(a, b);

        let tmp: BinaryPolynomial<U256> = BinaryPolynomial(Array::<u64, U4>(a)) * &Array(b).into();

        assert_eq!(c, tmp);

        let a = [0xaaaa_bbbb_cccc_dddd, 0x1999_8888_7777_6666];
        let b = [0xbc, 0x6f];

        let c: BinaryPolynomial<U127> =
            BinaryPolynomial(Array(a)).low_stack_mul(&mut BinaryPolynomial(Array(b)));
        // BinaryPolynomial::<U127>::low_stack_mult(&mut BinaryPolynomial(a, b);

        let tmp: BinaryPolynomial<U127> = BinaryPolynomial(Array::<u64, U2>(a)) * &Array(b).into();

        assert_eq!(c, tmp);

        // Not power of two length
        let a = [
            0xaaaa_bbbb_cccc_dddd,
            0x1999_8888_7777_6666,
            0x0000_0AAA_BBBB_8888,
        ];
        let b = [0xbc, 0x6f, 0x33];

        let c: BinaryPolynomial<U175> =
            BinaryPolynomial(Array(a)).low_stack_mul(&mut BinaryPolynomial(Array(b)));
        // BinaryPolynomial::<U127>::low_stack_mult(&mut BinaryPolynomial(a, b);

        let tmp: BinaryPolynomial<U175> = BinaryPolynomial(Array::<u64, U3>(a)) * &Array(b).into();

        assert_eq!(c, tmp);
    }

    #[test]
    fn test_low_stack_mult_hqc() {
        for i in 0..10 {
            test_low_stack_mult_hqc_sizes::<Hqc1>(1337);
            test_low_stack_mult_hqc_sizes::<Hqc3>(1437 + i);
            test_low_stack_mult_hqc_sizes::<Hqc5>(1537 + i);
        }
    }

    fn test_low_stack_mult_hqc_sizes<Hqc: PkeParams>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut xof = XofState::new(&rng.random::<[u8; 16]>());

        let mut a = xof.sample_vect::<Hqc>();
        let mut b = xof.sample_vect::<Hqc>();

        assert_eq!(a.low_stack_mul(&mut b), a * &b);
    }

    #[test]
    fn test_cumulative_karatsuba_basic() {
        let mut c = [0, 0, 0, 0];
        let mut a = [0xaaaa_bbbb_cccc_dddd, 0x1999_8888_7777_6666];
        let a2 = a.clone();
        let mut b = [0x1, 0x0];
        let b2 = b.clone();

        karatsuba_multiplication::cumulative_karatsuba(&mut c, &mut a, &mut b);
        assert_eq!(c[2..], [0, 0]);
        assert_eq!(c[..2], a);

        assert_eq!(a, a2);
        assert_eq!(b, b2);

        c[..2].copy_from_slice(&a);
        karatsuba_multiplication::cumulative_karatsuba(&mut c, &mut a, &mut b);
        assert_eq!(c, [0, 0, 0, 0]);

        assert_eq!(a, a2);
        assert_eq!(b, b2);

        let mut a = [0xaaaa_bbbb_cccc_dddd, 0x1999_8888_7777_6666, 0, 0];
        let a2 = a.clone();
        let mut b = [0xbc, 0x6f, 0, 0];
        let mut c = [0; 8];
        let b2 = b.clone();

        karatsuba_multiplication::cumulative_karatsuba(&mut c, &mut a, &mut b);

        assert_eq!(a, a2);
        assert_eq!(b, b2);

        assert_eq!(
            c[..4],
            [
                6151391603457855852,
                3692632457827516510,
                15371855257680893301,
                5
            ]
        );
    }

    #[test]
    fn test_cumulative_karatsuba_hqc() {
        for i in 0..10 {
            test_cumulative_karatsuba_hqc_sizes::<Hqc1>(1337);
            test_cumulative_karatsuba_hqc_sizes::<Hqc3>(1437 + i);
            test_cumulative_karatsuba_hqc_sizes::<Hqc5>(1537 + i);
        }
    }

    fn schoolbook_mult(c: &mut [u64], a: &[u64], b: &[u64]) {
        for i in 0..a.len() * 64 {
            let ai = (a[i / 64] >> (i % 64)) & 1;
            for j in 0..b.len() * 64 {
                let bj = (b[j / 64] >> (j % 64)) & 1;
                c[(i + j) / 64] ^= (ai & bj) << ((i + j) % 64);
            }
        }
    }

    fn test_cumulative_karatsuba_hqc_sizes<Hqc: PkeParams>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut xof = XofState::new(&rng.random::<[u8; 16]>());

        let mut a = xof.sample_vect::<Hqc>();
        let a2 = a.clone();
        let mut b = xof.sample_vect::<Hqc>();
        let b2 = b.clone();

        let mut c_karatsuba = Array::<u64, Prod<Octobytesize<Hqc::NBits>, U2>>::default();
        let mut c_schoolbook = c_karatsuba.clone();

        karatsuba_multiplication::cumulative_karatsuba(&mut c_karatsuba, &mut a.0, &mut b.0);
        assert_eq!(a2, a);
        assert_eq!(b2, b);

        schoolbook_mult(&mut c_schoolbook, &a.0, &b.0);

        assert_eq!(c_schoolbook, c_karatsuba);
    }

    // TODO: test from + into array of bytes
}
