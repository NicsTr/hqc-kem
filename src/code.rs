use core::ops::Mul;

use hybrid_array::{
    Array, ArraySize,
    typenum::{Prod, Unsigned},
};
use zerocopy::{FromBytes, Immutable, IntoBytes};

use crate::code::{
    reed_muller::{HQC1ReedMuller, HQC3ReedMuller, HQC5ReedMuller, InternalCode},
    reed_solomon::{ExternalCode, HQC1ReedSolomon, HQC3ReedSolomon, HQC5ReedSolomon},
};

mod gf256;
pub mod reed_muller;
pub mod reed_solomon;

/// A `Code` is something that encodes a `KBytes` message into
/// an `NBytes` codeword.
///
/// Interface for the error-correcting code used in HQC
pub(crate) trait Code {
    type KBytes: ArraySize;
    type NBytes: ArraySize;

    type Message: IntoBytes + Immutable + From<Array<u8, Self::KBytes>>;
    type Codeword: IntoBytes + From<Array<u8, Self::NBytes>> + FromBytes + Immutable;

    fn encode_once(message: &Self::Message) -> Self::Codeword;
    fn decode_once(codeword: &Self::Codeword) -> Self::Message;
}

pub(crate) trait Concatenated
where
    <Self::InternalCode as InternalCode>::NBytes: Mul<<Self::ExternalCode as ExternalCode>::N>,
    Prod<<Self::InternalCode as InternalCode>::NBytes, <Self::ExternalCode as ExternalCode>::N>:
        ArraySize,
    <<Self::ExternalCode as ExternalCode>::KBytes as ArraySize>::ArrayType<u8>:
        IntoBytes + Immutable,
    <<Self::ExternalCode as ExternalCode>::N as ArraySize>::ArrayType<
        <Self::InternalCode as InternalCode>::Codeword,
    >: IntoBytes + FromBytes + Immutable,
{
    type InternalCode: InternalCode;
    type ExternalCode: ExternalCode<CodewordElement = <Self::InternalCode as InternalCode>::Message>;
}

#[derive(Clone, IntoBytes, FromBytes, Immutable)]
#[repr(transparent)]
pub(crate) struct ConcatenatedCodeword<ICode: InternalCode, ECode: ExternalCode>(
    Array<ICode::Codeword, ECode::N>,
);

impl<ICode: InternalCode, ECode: ExternalCode> From<Array<u8, Prod<ICode::NBytes, ECode::N>>>
    for ConcatenatedCodeword<ICode, ECode>
where
    ICode::NBytes: Mul<ECode::N>,
    Prod<ICode::NBytes, ECode::N>: ArraySize,
{
    // TODO: Check that we do not lose to much performance here (think about using Zerocopy)
    fn from(value: Array<u8, Prod<ICode::NBytes, ECode::N>>) -> Self {
        let icode_nbytes = <ICode::NBytes as Unsigned>::USIZE;
        Self(Array::from_fn(|i| {
            let tmp: Array<u8, ICode::NBytes> = value[icode_nbytes * i..icode_nbytes * (i + 1)]
                .try_into()
                // Cannot fail since slice is correctly computed
                .unwrap();

            tmp.into()
        }))
    }
}

impl<C: Concatenated> Code for C {
    type KBytes = <C::ExternalCode as ExternalCode>::KBytes;
    type NBytes =
        Prod<<C::InternalCode as InternalCode>::NBytes, <C::ExternalCode as ExternalCode>::N>;

    type Message = Array<u8, <C::ExternalCode as ExternalCode>::KBytes>;
    // type Message = ConcatenatedMessage<C::ExternalCode>;
    type Codeword = ConcatenatedCodeword<C::InternalCode, C::ExternalCode>;

    fn encode_once(message: &Self::Message) -> Self::Codeword {
        ConcatenatedCodeword(C::InternalCode::encode_array(
            &C::ExternalCode::encode_bytes(message),
        ))
    }

    fn decode_once(codeword: &Self::Codeword) -> Self::Message {
        C::ExternalCode::decode_to_bytes(&C::InternalCode::decode_array(&codeword.0))
    }
}

pub(crate) struct HQC1Code;
pub(crate) struct HQC3Code;
pub(crate) struct HQC5Code;

impl Concatenated for HQC1Code {
    type InternalCode = HQC1ReedMuller;
    type ExternalCode = HQC1ReedSolomon;
}

impl Concatenated for HQC3Code {
    type InternalCode = HQC3ReedMuller;
    type ExternalCode = HQC3ReedSolomon;
}

impl Concatenated for HQC5Code {
    type InternalCode = HQC5ReedMuller;
    type ExternalCode = HQC5ReedSolomon;
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::XofState;
    use hybrid_array::sizes::{U2880, U4896, U8516, U17088, U35664, U49856};
    use rand::{Rng, RngCore, SeedableRng, rngs::StdRng};

    fn test_perfect_channel<C: Code>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..=300 {
            let mut message = Array::<u8, C::KBytes>::default();
            rng.fill_bytes(&mut message);
            let codeword = C::encode_once(&message.clone().into());

            assert_eq!(message.as_bytes(), C::decode_once(&codeword).as_bytes());
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
            let mut message = Array::<u8, C::KBytes>::default();
            rng.fill_bytes(&mut message);

            let mut codeword = C::encode_once(&message.clone().into());

            let noise = gen_binary_noise::<W, N>(&mut rng);
            for (i, v) in noise.iter().enumerate() {
                if *v {
                    codeword.as_mut_bytes()[i / 8] ^= 1 << (i % 8);
                }
            }

            assert_eq!(message.as_bytes(), C::decode_once(&codeword).as_bytes());
        }
    }

    fn test_from_into_bytes<C: Code>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut message_raw = Array::<u8, C::KBytes>::default();
        rng.fill_bytes(&mut message_raw);
        let message: <C as Code>::Message = message_raw.clone().into();

        assert_eq!(message_raw.as_bytes(), message.as_bytes());

        let mut codeword_raw = Array::<u8, C::NBytes>::default();
        rng.fill_bytes(&mut codeword_raw);
        let codeword: <C as Code>::Codeword = codeword_raw.clone().into();

        assert_eq!(codeword_raw.as_bytes(), codeword.as_bytes());
    }

    #[test]
    fn test_hqc1_noisy_channel() {
        // Slightly smaller noise length and weight, to use available sizes
        test_noisy_channel::<HQC1Code, U2880, U17088>(1437);
    }

    #[test]
    fn test_hqc3_noisy_channel() {
        // Slightly smaller noise length and weight, to use available sizes
        test_noisy_channel::<HQC3Code, U4896, U35664>(1438);
    }

    #[test]
    fn test_hqc5_noisy_channel() {
        // Slightly smaller noise length and weight, to use available sizes
        test_noisy_channel::<HQC5Code, U8516, U49856>(1439);
    }

    #[test]
    fn test_hqc1_perfect_channel() {
        test_perfect_channel::<HQC1Code>(1337);
    }

    #[test]
    fn test_hqc3_perfect_channel() {
        test_perfect_channel::<HQC3Code>(1338);
    }

    #[test]
    fn test_hqc5_perfect_channel() {
        test_perfect_channel::<HQC5Code>(1339);
    }

    #[test]
    fn test_hqc1_from_into_bytes() {
        test_from_into_bytes::<HQC1Code>(1537);
    }

    #[test]
    fn test_hqc3_from_into_bytes() {
        test_from_into_bytes::<HQC3Code>(1538);
    }

    #[test]
    fn test_hqc5_from_into_bytes() {
        test_from_into_bytes::<HQC5Code>(1539);
    }
}
