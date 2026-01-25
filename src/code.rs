use core::fmt::Debug;
use core::ops::Mul;

use hybrid_array::{
    Array, ArraySize,
    typenum::{Prod, Unsigned},
};

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

    type Message: From<Array<u8, Self::KBytes>> + Into<Array<u8, Self::KBytes>> + Debug;
    type Codeword: From<Array<u8, Self::NBytes>> + Into<Array<u8, Self::NBytes>>;

    fn encode_once(message: &Self::Message) -> Self::Codeword;
    fn decode_once(codeword: &Self::Codeword) -> Self::Message;

    fn encode_array<N: ArraySize>(messages: &Array<Self::Message, N>) -> Array<Self::Codeword, N> {
        Array::from_fn(|i| Self::encode_once(&messages[i]))
    }
    fn decode_array<N: ArraySize>(codewords: &Array<Self::Codeword, N>) -> Array<Self::Message, N> {
        Array::from_fn(|i| Self::decode_once(&codewords[i]))
    }
}

pub(crate) trait Concatenated {
    type InternalCode: InternalCode;
    type ExternalCode: ExternalCode<CodewordElement = <Self::InternalCode as InternalCode>::Message>;
}

#[derive(Clone)]
pub(crate) struct ConcatenatedCodeword<ICode: InternalCode, ECode: ExternalCode>(
    Array<ICode::Codeword, ECode::N>,
);

impl<ICode: InternalCode, ECode: ExternalCode> From<Array<u8, Prod<ICode::NBytes, ECode::N>>>
    for ConcatenatedCodeword<ICode, ECode>
where
    ICode::NBytes: Mul<ECode::N>,
    Prod<ICode::NBytes, ECode::N>: ArraySize,
{
    fn from(value: Array<u8, Prod<ICode::NBytes, ECode::N>>) -> Self {
        let icode_nbytes = <ICode::NBytes as Unsigned>::USIZE;
        Self(Array::from_fn(|i| {
            let tmp: Array<u8, ICode::NBytes> = value[icode_nbytes * i..icode_nbytes * (i + 1)]
                .try_into()
                .unwrap();

            tmp.into()
        }))
    }
}

impl<ICode: InternalCode, ECode: ExternalCode> From<ConcatenatedCodeword<ICode, ECode>>
    for Array<u8, Prod<ICode::NBytes, ECode::N>>
where
    ICode::NBytes: Mul<ECode::N>,
    Prod<ICode::NBytes, ECode::N>: ArraySize,
{
    fn from(value: ConcatenatedCodeword<ICode, ECode>) -> Self {
        let nested_array: Array<Array<u8, ICode::NBytes>, ECode::N> = value.0.map(|w| w.into());
        // Cannot fail since the flattened array is of the right size
        Array::<u8, Prod<ICode::NBytes, ECode::N>>::try_from(nested_array.as_flattened()).unwrap()
    }
}

impl<C: Concatenated> Code for C
where
    <C::InternalCode as InternalCode>::NBytes: Mul<<C::ExternalCode as ExternalCode>::N>,
    Prod<<C::InternalCode as InternalCode>::NBytes, <C::ExternalCode as ExternalCode>::N>:
        ArraySize,
{
    type KBytes = <C::ExternalCode as ExternalCode>::KBytes;
    type NBytes =
        Prod<<C::InternalCode as InternalCode>::NBytes, <C::ExternalCode as ExternalCode>::N>;

    type Message = <C::ExternalCode as ExternalCode>::Message;
    type Codeword = ConcatenatedCodeword<C::InternalCode, C::ExternalCode>;

    fn encode_once(message: &Self::Message) -> Self::Codeword {
        ConcatenatedCodeword(C::InternalCode::encode_array(
            &C::ExternalCode::encode_once(message),
        ))
    }

    fn decode_once(codeword: &Self::Codeword) -> Self::Message {
        C::ExternalCode::decode_once(&C::InternalCode::decode_array(&codeword.0))
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

// FIXME: require new sizes in hybrid_array (7200 for code length
// impl Concatenated for HQC5Code {
//     type InternalCode = HQC5ReedMuller;
//     type ExternalCode = HQC5ReedSolomon;
// }

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::XofState;
    use hybrid_array::sizes::{U8, U2880, U4896, U17088, U35664};
    use rand::{Rng, RngCore, SeedableRng, rngs::StdRng};

    fn test_perfect_channel<C: Code>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..=300 {
            let mut message = Array::<u8, C::KBytes>::default();
            rng.fill_bytes(&mut message);
            let codeword = C::encode_once(&message.clone().into());

            assert_eq!(message, C::decode_once(&codeword).into());
        }
    }

    fn gen_binary_noise<W: ArraySize, N: ArraySize>(rng: &mut StdRng) -> Array<bool, N> {
        let seed: [u8; _] = rng.random();
        let mut xof = XofState::new::<U8>(&Array(seed));
        let support: Array<usize, W> = xof.generate_random_support::<W, N>();

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

            let codeword = C::encode_once(&message.clone().into());

            // Slightly smaller noise length, to use available sizes
            let noise = gen_binary_noise::<W, N>(&mut rng);

            let mut noisy_codeword: Array<_, _> = codeword.into();
            for (i, v) in noise.iter().enumerate() {
                if *v {
                    noisy_codeword[i / 8] ^= 1 << (i % 8);
                }
            }

            assert_eq!(message, C::decode_once(&noisy_codeword.into()).into());
        }
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

    // #[test]
    // fn test_hqc5_noisy_channel() {
    //     // Slightly smaller noise length and weight, to use available sizes
    //     test_noisy_channel::<HQC5Code, U8516, U49856>(1439);
    // }

    #[test]
    fn test_hqc1_perfect_channel() {
        test_perfect_channel::<HQC1Code>(1337);
    }

    #[test]
    fn test_hqc3_perfect_channel() {
        test_perfect_channel::<HQC3Code>(1338);
    }

    // #[test]
    // fn test_hqc5_perfect_channel() {
    //     test_perfect_channel::<HQC5Code>(1339);
    // }
}
