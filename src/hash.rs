use ctutils::{Choice, CtAssign, CtEq, CtLt, CtSelect};
use hybrid_array::{
    Array, ArraySize,
    sizes::{U8, U64},
    typenum::Unsigned,
};
use kem::{Kem, KeyExport};
use sha3::{
    Digest, Sha3_256, Sha3_512, Shake256, Shake256Reader,
    digest::{ExtendableOutput, Update, XofReader},
};
use zerocopy::IntoBytes;

use crate::{
    kem::Ciphertext, pke::PkeParams, polynomial::BinaryPolynomial, size_traits::WordsizeFromBitsize,
};

const XOF_DOMAIN_SEPARATOR: u8 = 1;
const G_DOMAIN_SEPARATOR: u8 = 0;
const H_DOMAIN_SEPARATOR: u8 = 1;
const I_DOMAIN_SEPARATOR: u8 = 2;
const J_DOMAIN_SEPARATOR: u8 = 3;

pub(crate) fn hash_g<P: PkeParams>(
    h: &[u8; 32],
    m: &Array<u8, P::ExternalMessageBytesize>,
    salt: &[u8; 16],
) -> [u8; 64] {
    Sha3_512::new()
        .chain_update(h)
        .chain_update(m.as_bytes())
        .chain_update(salt)
        .chain_update([G_DOMAIN_SEPARATOR])
        .finalize()
        .into()
}

pub(crate) fn hash_h<K: Kem>(ek: &K::EncapsulationKey) -> [u8; 32] {
    Sha3_256::new()
        .chain_update(ek.to_bytes())
        .chain_update([H_DOMAIN_SEPARATOR])
        .finalize()
        .into()
}

pub(crate) fn hash_i(input: &[u8; 32]) -> [u8; 64] {
    Sha3_512::new()
        .chain_update(input)
        .chain_update([I_DOMAIN_SEPARATOR])
        .finalize()
        .into()
}

pub(crate) fn hash_j<P: PkeParams>(
    h: &[u8; 32],
    rejection_randomness: &Array<u8, P::ExternalMessageBytesize>,
    ciphertext: &Ciphertext<P>,
) -> [u8; 32] {
    Sha3_256::new()
        .chain_update(h)
        .chain_update(rejection_randomness)
        .chain_update(Array::<u8, _>::from(ciphertext))
        .chain_update([J_DOMAIN_SEPARATOR])
        .finalize()
        .into()
}

/// Performs the constant-time Barret modular reduction of `value` modulo `N`.
fn barret_reduction<N: Unsigned>(value: u32) -> u32 {
    // Compile time verification that N is non-zero and computation of m.
    let m = const {
        assert!(N::U64 > 0);
        (1u64 << 32) / N::U64
    };

    // Both value and m fit in an u32, this multiplication is not overflowing
    // Result fits in u32 since it is shifted right by 32.
    let q: u32 = (((value as u64) * m) >> 32) as u32;

    // q * N is guaranteed to be smaller than value, so there is no underflow
    let mut res = value - (q * N::U32);

    // q may be one less than needed so we perform a constant-time conditionnal
    // subtraction by N.
    res -= u32::ct_select(&N::U32, &0u32, res.ct_lt(&N::U32));

    res
}

pub(crate) struct XofState(Shake256Reader);

impl XofState {
    pub(crate) fn new(seed: &[u8]) -> Self {
        XofState(
            Shake256::default()
                .chain(seed)
                .chain([XOF_DOMAIN_SEPARATOR])
                .finalize_xof(),
        )
    }

    pub(crate) fn get_bytes(&mut self, buf: &mut [u8]) {
        self.0.read(buf);
    }

    /// Generate a close-to-uniformly random u32 between 0 (inclusive) and `max` (exclusive).
    ///
    /// The non-uniformity and its impact is discussed in https://eprint.iacr.org/2021/1631
    /// and in Section 6.2.3 of the HQC proposal.
    //
    // TODO: The reference implementation is different from the specification. We chose to
    // implement according to the reference implementation to use their test vectors.
    // This should be checked against FIPS-207, when it is released.
    fn get_randint(&mut self, max: u32) -> u32 {
        let mut rand_buf = [0u8; 4];
        self.get_bytes(&mut rand_buf);
        ((u32::from_le_bytes(rand_buf) as u64 * max as u64) >> 32) as u32
    }

    /// Generate a support for a random `N`-elements vector of weight `W`
    /// *uniformly* at random using this XOF and rejection sampling.
    ///
    // TODO: HQC specification seems to use rejection sampler in some places and
    // biased sampler in others, without really explaining why. Also, rejection sampling
    // is not described in details in the specification. This implementation is based on
    // the reference implementation. This most certainly will need to be updated when
    // FIPS-207 is released.
    pub(crate) fn generate_random_support_rejection<W: ArraySize, N: Unsigned>(
        &mut self,
    ) -> Array<usize, W> {
        let rejection_threshold = const {
            // Check that N is valid
            assert!(N::USIZE > 0);
            assert!(N::USIZE < (1 << 24));

            // Compute the threshold to be the largest multiple of N
            // not overflowing the maximum integer drawn at random each time.
            ((1 << 24) / N::U32) * N::U32
        };

        let mut res = Array::default();
        let mut rand_bytes = [0u8; 4];
        let mut i = 0;
        while i < W::USIZE {
            // Bytes are fetched only three at a time, and used in big-endian.
            // To accomodate with `from_be_bytes()` needing an array of length 4,
            // the first byte of rand_bytes is never set.
            self.get_bytes(&mut rand_bytes[1..]);
            let candidate = u32::from_be_bytes(rand_bytes);
            if candidate > rejection_threshold {
                continue;
            }

            let reduced_candidate = barret_reduction::<N>(candidate) as usize;
            if res[..i].contains(&reduced_candidate) {
                continue;
            }

            res[i] = reduced_candidate;
            i += 1;
        }

        res
    }

    /// Generate a random support for a random `N`-elements vector of weight `W`
    /// in *constant time* using this XOF, based on the Fisher-Yates random shuffle.
    ///
    /// This process does not follow a perfectly uniform distribution and an analysis
    /// its bias can be found in Sendrier's work (https://eprint.iacr.org/2021/1631) and
    /// its impact on the security of HQC is further discussed in Section 6.2.3 of
    /// the HQC proposal.
    pub(crate) fn generate_random_support_biased<W: ArraySize, N: Unsigned>(
        &mut self,
    ) -> Array<usize, W> {
        // Initialize result, without taking into account collisions
        let mut res = Array::from_fn(|i| i + self.get_randint(N::U32 - (i as u32)) as usize);

        // When a collision occured, replace the value by the index of collision.
        for i in (0..W::USIZE).rev() {
            let mut collision = Choice::FALSE;

            for j in (i + 1)..W::USIZE {
                collision |= res[i].ct_eq(&res[j]);
            }

            // In case of collision at the i-th step, set the index to i
            res[i].ct_assign(&i, collision);
        }

        res
    }

    pub(crate) fn sample_fixed_weight_vect_rejection<
        W: ArraySize,
        NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>,
    >(
        &mut self,
    ) -> BinaryPolynomial<NBits> {
        let mut res = BinaryPolynomial::zero();

        for v in self.generate_random_support_rejection::<W, NBits>() {
            res.set_coefficient(v);
        }

        res
    }

    /// Sample a fixed weight bin.
    pub(crate) fn sample_fixed_weight_vect_biased<
        W: ArraySize,
        NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>,
    >(
        &mut self,
    ) -> BinaryPolynomial<NBits> {
        let mut res = BinaryPolynomial::zero();

        for v in self.generate_random_support_biased::<W, NBits>() {
            res.set_coefficient(v);
        }

        res
    }

    /// Sample a vector uniformly at random.
    pub(crate) fn sample_vect<NBits: WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>>(
        &mut self,
    ) -> BinaryPolynomial<NBits> {
        Array::from_fn(|_| {
            let mut buf: [u8; 8] = Default::default();
            self.0.read(&mut buf);
            u64::from_le_bytes(buf)
        })
        .into()
    }
}

#[cfg(test)]
mod test {
    use hybrid_array::sizes::{U1, U10, U100, U124, U128};
    use hybrid_array::typenum::consts::U4294967295;

    use super::{XofState, barret_reduction};

    #[test]
    fn test_generate_random_support_biased() {
        let mut xof = XofState::new(&[13u8, 37u8]);

        for _ in 0..10000 {
            let support = xof.generate_random_support_biased::<U10, U100>();

            for i in 0..10 {
                let index = support[i];

                // Check that index is always in range
                assert!(index < 100);

                // Check that support is a set
                for j in i + 1..10 {
                    assert_ne!(index, support[j]);
                }
            }
        }
    }

    #[test]
    fn test_generate_random_support_rejection() {
        let mut xof = XofState::new(&[13u8, 38u8]);

        for _ in 0..10000 {
            let support = xof.generate_random_support_rejection::<U10, U100>();

            for i in 0..10 {
                let index = support[i];

                // Check that index is always in range
                assert!(index < 100);

                // Check that support is a set
                for j in i + 1..10 {
                    assert_ne!(index, support[j]);
                }
            }
        }
    }

    #[test]
    fn test_randint() {
        let mut xof = XofState::new(&[13u8, 39u8]);

        for _ in 0..1000 {
            let value = xof.get_randint(40);
            // Simple sanity check
            assert!(value < 40);
        }
    }

    #[test]
    fn test_barret_reduction() {
        for i in 0..(1 << 12) {
            assert_eq!(barret_reduction::<U124>(i), i % 124);
            assert_eq!(barret_reduction::<U128>(i), i % 128);
            assert_eq!(barret_reduction::<U1>(i), i % 1);
            // u32::MAX
            assert_eq!(barret_reduction::<U4294967295>(i), i % 4294967295);
        }
    }
}
