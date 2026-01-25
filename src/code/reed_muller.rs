use core::{array, ops::Mul};

use hybrid_array::{
    Array, ArraySize,
    sizes::{U3, U5, U16},
    typenum::{Prod, Unsigned},
};

use ctutils::{Choice, CtAssign, CtEq, CtGt, CtNeg, CtSelect};

// FIXME: restrict visibility before publishing

/// An `InternalCode` is something that encodes a message into
/// an `NBytes` bytes codeword. The message is meant
/// to come from the encoding by an `ExternalCode`.
pub trait InternalCode {
    type NBytes: ArraySize;

    type Message;
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

pub trait DuplicatedReedMuller17Param
where
    Self::M: Mul<U16>,
    Prod<Self::M, U16>: ArraySize,
{
    type M: ArraySize;

    fn broadcast(bit: bool) -> u128 {
        // FIXME: look into (2*128).wrapping_neg()
        (bit as u128).wrapping_neg()
    }

    // Step 0. Accumulate every duplicated codeword as one state
    fn accumulate(codeword: &RMCodeword<Self::M>) -> ReedMuller17AccumulatedState {
        array::from_fn(|i| codeword.0.iter().map(|ci| ((ci >> i) & 1) as i16).sum())
    }

    #[inline(always)]
    fn green_machine_stage(
        src: &ReedMuller17AccumulatedState,
        dst: &mut ReedMuller17AccumulatedState,
    ) {
        for i in 0..64 {
            dst[i] = src[2 * i] + src[2 * i + 1];
            dst[i + 64] = src[2 * i] - src[2 * i + 1];
        }
    }

    // Step 1. Computing Walsh-Hadamard transform applied to each coordinate,
    // using the Fast Walsh-Hadamard algorithm
    fn walsh_hadamard(
        mut accumulated: ReedMuller17AccumulatedState,
    ) -> ReedMuller17AccumulatedState {
        let mut tmp = [0; 128];

        Self::green_machine_stage(&accumulated, &mut tmp);
        Self::green_machine_stage(&tmp, &mut accumulated);
        Self::green_machine_stage(&accumulated, &mut tmp);
        Self::green_machine_stage(&tmp, &mut accumulated);
        Self::green_machine_stage(&accumulated, &mut tmp);
        Self::green_machine_stage(&tmp, &mut accumulated);
        Self::green_machine_stage(&accumulated, &mut tmp);

        tmp[0] -= 64 * <Self::M as Unsigned>::I16;
        tmp
    }

    /// Step 2. Find the highest absolute value and correct for sign
    ///
    /// Be carefule to do it in constant time.
    fn find_max(transformed: &ReedMuller17AccumulatedState) -> u8 {
        let mut max_abs = 0;
        let mut max_i = 0;
        let mut max_is_negative = Choice::FALSE;

        for (i, vi) in transformed.iter().enumerate() {
            // signed right shift is arithmetic right shift
            let is_negative = (vi >> 15).ct_ne(&0);
            let abs = vi.ct_neg(is_negative) as u16;

            max_i.ct_assign(&(i as u8), abs.ct_gt(&max_abs));
            max_is_negative.ct_assign(&is_negative, abs.ct_gt(&max_abs));
            max_abs.ct_assign(&abs, abs.ct_gt(&max_abs));
        }
        (max_i | 128).ct_select(&max_i, max_is_negative)
    }
}

pub struct HQC1ReedMuller;
pub struct HQC3ReedMuller;
pub struct HQC5ReedMuller;

impl DuplicatedReedMuller17Param for HQC1ReedMuller {
    type M = U3;
}
impl DuplicatedReedMuller17Param for HQC3ReedMuller {
    type M = U5;
}
impl DuplicatedReedMuller17Param for HQC5ReedMuller {
    type M = U5;
}

type ReedMuller17AccumulatedState = [i16; 128];

pub struct RMCodeword<M: ArraySize>(Array<u128, M>);

impl<M: ArraySize> From<Array<u8, Prod<M, U16>>> for RMCodeword<M>
where
    M: Mul<U16>,
    Prod<M, U16>: ArraySize,
{
    fn from(value: Array<u8, Prod<M, U16>>) -> Self {
        Self(Array::from_fn(|i| {
            // Cannot fail since the slice is of the right size
            u128::from_be_bytes(value[16 * i..16 * (i + 1)].try_into().unwrap())
        }))
    }
}

impl<M: ArraySize> From<RMCodeword<M>> for Array<u8, Prod<M, U16>>
where
    M: Mul<U16>,
    Prod<M, U16>: ArraySize,
{
    fn from(value: RMCodeword<M>) -> Self {
        let nested_array: Array<_, M> =
            // U16 = U128/u8::BITS
            Array::from_fn(|i| Array::<u8, U16>(value.0[i].to_be_bytes()));
        // Cannot fail since the flattened array is of the right size
        Array::<u8, Prod<M, U16>>::try_from(nested_array.as_flattened()).unwrap()
    }
}

impl<RM: DuplicatedReedMuller17Param> InternalCode for RM
where
    RM::M: Mul<U16>,
    Prod<RM::M, U16>: ArraySize,
{
    type NBytes = Prod<RM::M, U16>;

    type Message = u8;
    type Codeword = RMCodeword<RM::M>;

    /// Message encoding using RM(1, 7) code
    fn encode_once(message: &Self::Message) -> Self::Codeword {
        // RM(1, 7) generator matrix multiplication
        let mut res = Self::broadcast(((message >> 7) & 1) == 1u8);

        res ^= Self::broadcast((message & 1) == 1u8) & 0xaaaaaaaa_aaaaaaaa_aaaaaaaa_aaaaaaaa;
        res ^= Self::broadcast(((message >> 1) & 1) == 1u8) & 0xcccccccc_cccccccc_cccccccc_cccccccc;
        res ^= Self::broadcast(((message >> 2) & 1) == 1u8) & 0xf0f0f0f0_f0f0f0f0_f0f0f0f0_f0f0f0f0;
        res ^= Self::broadcast(((message >> 3) & 1) == 1u8) & 0xff00ff00_ff00ff00_ff00ff00_ff00ff00;
        res ^= Self::broadcast(((message >> 4) & 1) == 1u8) & 0xffff0000_ffff0000_ffff0000_ffff0000;
        res ^= Self::broadcast(((message >> 5) & 1) == 1u8) & 0xffffffff_00000000_ffffffff_00000000;
        res ^= Self::broadcast(((message >> 6) & 1) == 1u8) & 0xffffffff_ffffffff_00000000_00000000;

        RMCodeword(Array::from_fn(|_| res))
    }
    /// Message decoding for an RM(1, 7) codeword using Hadamard decoding.
    /// From MacWilliams and Sloane, 1977, Chapter 14
    fn decode_once(codeword: &Self::Codeword) -> Self::Message {
        let transformed = Self::walsh_hadamard(Self::accumulate(codeword));
        Self::find_max(&transformed)
    }
}

// FIXME: cleanup
pub trait DecodeOptim: InternalCode {
    fn decode_optim(codeword: Self::Codeword) -> Self::Message;
}

const RM17_GEN_MATRIX: [u128; 8] = [
    0xaaaaaaaa_aaaaaaaa_aaaaaaaa_aaaaaaaa,
    0xcccccccc_cccccccc_cccccccc_cccccccc,
    0xf0f0f0f0_f0f0f0f0_f0f0f0f0_f0f0f0f0,
    0xff00ff00_ff00ff00_ff00ff00_ff00ff00,
    0xffff0000_ffff0000_ffff0000_ffff0000,
    0xffffffff_00000000_ffffffff_00000000,
    0xffffffff_ffffffff_00000000_00000000,
    0xffffffff_ffffffff_ffffffff_ffffffff,
];

impl<RM: DuplicatedReedMuller17Param> DecodeOptim for RM {
    /// Gray decoding
    fn decode_optim(mut codeword: Self::Codeword) -> Self::Message {
        let mut current_message = 0;

        let mut distances: ReedMuller17AccumulatedState = [-64 * RM::M::I16; 128];

        for counter in 1..129u8 {
            let gray_index = counter.trailing_zeros() as usize;
            for m in 0..RM::M::USIZE {
                distances[current_message] += codeword.0[m].count_ones() as i16;

                codeword.0[m] ^= RM17_GEN_MATRIX[gray_index];
            }
            current_message ^= 1 << gray_index;
        }

        Self::find_max(&distances)
    }
}

#[cfg(test)]
mod test {
    use core::ops::Div;

    use crate::utils::XofState;

    use super::*;
    use hybrid_array::{
        sizes::{U2, U8, U128},
        typenum::Quot,
    };
    use rand::{Rng, SeedableRng, rngs::StdRng};

    fn test_reed_muller_perfect_channel<RM: DuplicatedReedMuller17Param>() {
        for i in 0..=255 {
            let codeword = RM::encode_once(&i);

            assert_eq!(i, RM::decode_once(&codeword));
        }
    }

    fn test_reed_muller_perfect_channel_optim<RM: DuplicatedReedMuller17Param>() {
        for i in 0..=255 {
            let codeword = RM::encode_once(&i);

            assert_eq!(i, RM::decode_optim(codeword));
        }
    }

    fn gen_noise<M: ArraySize + Div<U2> + Mul<U128>>(rng: &mut StdRng) -> RMCodeword<M>
    where
        Prod<M, U128>: ArraySize,
        Quot<M, U2>: ArraySize,
    {
        let seed: [u8; _] = rng.random();
        let mut xof = XofState::new::<U8>(&Array(seed));
        let support: Array<usize, Quot<M, U2>> =
            xof.generate_random_support::<Quot<M, U2>, Prod<M, U128>>();

        let mut res = Array::default();
        for v in support {
            res[v / 128] |= 1 << (v % 128);
        }
        println!("{res:?}");
        RMCodeword(res)
    }

    fn xor_noise<M: ArraySize>(codeword: &mut RMCodeword<M>, noise: &RMCodeword<M>) {
        codeword
            .0
            .iter_mut()
            .zip(&noise.0)
            .for_each(|(c, n)| *c ^= n);
    }

    fn test_reed_muller_noisy_channel<RM: DuplicatedReedMuller17Param>(seed: u64)
    where
        RM::M: Mul<U128> + Div<U2>,
        Prod<RM::M, U128>: ArraySize,
        Quot<RM::M, U2>: ArraySize,
    {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..10000 {
            let message: u8 = rng.random();
            let noise = gen_noise::<RM::M>(&mut rng);

            let mut codeword = RM::encode_once(&(message));

            xor_noise::<RM::M>(&mut codeword, &noise);

            assert_eq!(message, RM::decode_once(&codeword));
        }
    }

    fn test_reed_muller_noisy_channel_optim<RM: DuplicatedReedMuller17Param>(seed: u64)
    where
        RM::M: Mul<U128> + Div<U2>,
        Prod<RM::M, U128>: ArraySize,
        Quot<RM::M, U2>: ArraySize,
    {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..10000 {
            let message: u8 = rng.random();
            let noise = gen_noise::<RM::M>(&mut rng);

            let mut codeword = RM::encode_once(&(message));

            xor_noise::<RM::M>(&mut codeword, &noise);

            assert_eq!(message, RM::decode_optim(codeword));
        }
    }

    #[test]
    fn test_perfect_hqc1rm() {
        test_reed_muller_perfect_channel::<HQC1ReedMuller>();
    }

    #[test]
    fn test_perfect_hqc3rm() {
        test_reed_muller_perfect_channel::<HQC3ReedMuller>();
    }

    #[test]
    fn test_perfect_hqc5rm() {
        test_reed_muller_perfect_channel::<HQC5ReedMuller>();
    }

    #[test]
    fn test_perfect_optim_hqc1rm() {
        test_reed_muller_perfect_channel_optim::<HQC1ReedMuller>();
    }

    #[test]
    fn test_perfect_optim_hqc3rm() {
        test_reed_muller_perfect_channel_optim::<HQC3ReedMuller>();
    }

    #[test]
    fn test_perfect_optim_hqc5rm() {
        test_reed_muller_perfect_channel_optim::<HQC5ReedMuller>();
    }

    #[test]
    fn test_noisy_hqc1rm() {
        test_reed_muller_noisy_channel::<HQC1ReedMuller>(1337);
    }

    #[test]
    fn test_noisy_hqc3rm() {
        test_reed_muller_noisy_channel::<HQC3ReedMuller>(1338);
    }

    #[test]
    fn test_noisy_hqc5rm() {
        test_reed_muller_noisy_channel::<HQC5ReedMuller>(1339);
    }

    #[test]
    fn test_noisy_optim_hqc1rm() {
        test_reed_muller_noisy_channel_optim::<HQC1ReedMuller>(1337);
    }

    #[test]
    fn test_noisy_optim_hqc3rm() {
        test_reed_muller_noisy_channel_optim::<HQC3ReedMuller>(1338);
    }

    #[test]
    fn test_noisy_optim_hqc5rm() {
        test_reed_muller_noisy_channel_optim::<HQC5ReedMuller>(1339);
    }
}
