use core::ops::Mul;

use hybrid_array::{
    Array, ArraySize,
    typenum::{Prod, Unsigned},
};

use crate::code::{
    reed_muller::{DuplicatedReedMuller17Param, InternalCode},
    reed_solomon::{ExternalCode, ShortenedByteReedSolomonParam},
};

mod gf256;
mod reed_muller;
mod reed_solomon;

pub trait CodeParams: ShortenedByteReedSolomonParam + DuplicatedReedMuller17Param {
    type CodewordBytesize: ArraySize;
}

impl<C: ShortenedByteReedSolomonParam + DuplicatedReedMuller17Param> CodeParams for C
where
    Self::InternalCodewordBytesize: Mul<Self::ExternalCodewordBytesize>,
    Prod<Self::InternalCodewordBytesize, Self::ExternalCodewordBytesize>: ArraySize,
{
    type CodewordBytesize = Prod<C::InternalCodewordBytesize, C::ExternalCodewordBytesize>;
}

/// A `Code` is something that encodes a `KBytes` message into
/// an `NBytes` codeword.
///
/// Interface for the error-correcting code used in HQC
pub(crate) trait Code: CodeParams {
    fn encode(
        message: &Array<u8, Self::ExternalMessageBytesize>,
    ) -> Array<u8, Self::CodewordBytesize> {
        const {
            assert!(
                Self::CodewordBytesize::USIZE.is_multiple_of(Self::InternalCodewordBytesize::USIZE)
            )
        }

        // TODO: Check that there is not too much copy here
        // TODO: Maybe use .flatten
        let mut res = Array::default();
        for (a, b) in res
            .chunks_exact_mut(Self::InternalCodewordBytesize::USIZE)
            .zip(Self::encode_external(message))
        {
            a.copy_from_slice(&Self::encode_internal(&b)[..]);
        }
        res
    }

    fn decode(
        codeword: &Array<u8, Self::CodewordBytesize>,
    ) -> Array<u8, Self::ExternalMessageBytesize> {
        const {
            assert!(
                Self::CodewordBytesize::USIZE.is_multiple_of(Self::InternalCodewordBytesize::USIZE)
            )
        }

        // TODO: Check that there is not too much copy here
        // TODO: Maybe use .unflatten
        let mut external_codeword = Array::default();
        for (a, b) in codeword
            .chunks_exact(Self::InternalCodewordBytesize::USIZE)
            .zip(external_codeword.iter_mut())
        {
            let mut internal_codeword = Array::default();
            // Cannot panic since slices are equal size (guaranteed by chunk exact)
            internal_codeword[..].copy_from_slice(a);
            *b = Self::decode_internal(&internal_codeword)
        }

        Self::decode_external(&external_codeword)
    }
}

impl<C: CodeParams> Code for C {}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{Hqc1, Hqc3, Hqc5, hash::XofState};
    use hybrid_array::sizes::{U2880, U4896, U8516, U17088, U35664, U49856};
    use rand::{Rng, RngExt, SeedableRng, rngs::StdRng};
    use zerocopy::IntoBytes;

    fn test_perfect_channel<C: Code>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..=300 {
            let mut message = Array::<u8, C::ExternalMessageBytesize>::default();
            rng.fill_bytes(&mut message);
            let codeword = C::encode(&message);

            assert_eq!(message.as_bytes(), C::decode(&codeword).as_bytes());
        }
    }

    fn gen_binary_noise<W: ArraySize, N: ArraySize>(rng: &mut StdRng) -> Array<bool, N> {
        let seed: [u8; 8] = rng.random();
        let mut xof = XofState::new(&seed);
        let support: Array<usize, W> = xof.generate_random_support_biased::<W, N>();

        let mut res = Array::default();
        for v in support {
            res[v] = true;
        }
        res
    }

    fn test_noisy_channel<C: Code, W: ArraySize, N: ArraySize>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..=100 {
            let mut message = Array::<u8, C::ExternalMessageBytesize>::default();
            rng.fill_bytes(&mut message);

            let mut codeword = C::encode(&message.clone());

            let noise = gen_binary_noise::<W, N>(&mut rng);
            for (i, v) in noise.iter().enumerate() {
                if *v {
                    codeword.as_mut_bytes()[i / 8] ^= 1 << (i % 8);
                }
            }

            assert_eq!(message, C::decode(&codeword));
        }
    }

    #[test]
    fn test_hqc1_noisy_channel() {
        // Slightly smaller noise length and weight, to use available sizes
        test_noisy_channel::<Hqc1, U2880, U17088>(1437);
    }

    #[test]
    fn test_hqc3_noisy_channel() {
        // Slightly smaller noise length and weight, to use available sizes
        test_noisy_channel::<Hqc3, U4896, U35664>(1438);
    }

    #[test]
    fn test_hqc5_noisy_channel() {
        // Slightly smaller noise length and weight, to use available sizes
        test_noisy_channel::<Hqc5, U8516, U49856>(1439);
    }

    #[test]
    fn test_hqc1_perfect_channel() {
        test_perfect_channel::<Hqc1>(1337);
    }

    #[test]
    fn test_hqc3_perfect_channel() {
        test_perfect_channel::<Hqc3>(1338);
    }

    #[test]
    fn test_hqc5_perfect_channel() {
        test_perfect_channel::<Hqc5>(1339);
    }
}
