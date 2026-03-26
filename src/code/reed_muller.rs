use core::{array, ops::Mul};

use hybrid_array::{
    Array, ArraySize,
    sizes::{U3, U5, U16},
    typenum::{Prod, Unsigned},
};

use ctutils::{Choice, CtAssign, CtEq, CtGt, CtNeg, CtSelect};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

use crate::{Hqc1, Hqc3, Hqc5};

impl DuplicatedReedMuller17Param for Hqc1 {
    type M = U3;

    type InternalCodewordBytesize = Prod<Self::M, U16>;
}

impl DuplicatedReedMuller17Param for Hqc3 {
    type M = U5;
    type InternalCodewordBytesize = Prod<Self::M, U16>;
}

impl DuplicatedReedMuller17Param for Hqc5 {
    type M = U5;
    type InternalCodewordBytesize = Prod<Self::M, U16>;
}

// Parameter and implementation have different visibilities
pub trait DuplicatedReedMuller17Param: Clone
where
    Self::M: Mul<U16>,
    Prod<Self::M, U16>: ArraySize,
    <Self::M as ArraySize>::ArrayType<u128>: IntoBytes + FromBytes + Immutable + KnownLayout,
    <Prod<Self::M, U16> as ArraySize>::ArrayType<u8>:
        IntoBytes + FromBytes + Immutable + KnownLayout,
    <Self::InternalCodewordBytesize as ArraySize>::ArrayType<u8>:
        IntoBytes + FromBytes + Immutable + KnownLayout,
{
    type M: ArraySize;
    type InternalCodewordBytesize: ArraySize;
}

/// An `InternalCode` is something that encodes a byte into
/// an `NBytes` bytes codeword.
pub(crate) trait InternalCode: DuplicatedReedMuller17 {
    /// Message encoding using RM(1, 7) code
    fn encode_internal(message: &u8) -> Array<u8, Self::InternalCodewordBytesize> {
        // RM(1, 7) generator matrix multiplication
        let mut res = Self::broadcast(((message >> 7) & 1) == 1u8);

        res ^= Self::broadcast((message & 1) == 1u8) & 0xaaaaaaaa_aaaaaaaa_aaaaaaaa_aaaaaaaa;
        res ^= Self::broadcast(((message >> 1) & 1) == 1u8) & 0xcccccccc_cccccccc_cccccccc_cccccccc;
        res ^= Self::broadcast(((message >> 2) & 1) == 1u8) & 0xf0f0f0f0_f0f0f0f0_f0f0f0f0_f0f0f0f0;
        res ^= Self::broadcast(((message >> 3) & 1) == 1u8) & 0xff00ff00_ff00ff00_ff00ff00_ff00ff00;
        res ^= Self::broadcast(((message >> 4) & 1) == 1u8) & 0xffff0000_ffff0000_ffff0000_ffff0000;
        res ^= Self::broadcast(((message >> 5) & 1) == 1u8) & 0xffffffff_00000000_ffffffff_00000000;
        res ^= Self::broadcast(((message >> 6) & 1) == 1u8) & 0xffffffff_ffffffff_00000000_00000000;

        Array::<u8, Self::InternalCodewordBytesize>::read_from_bytes(
            Array::<u128, Self::M>::from_fn(|_| res).as_bytes(),
        )
        // Cannot panic since size is correct
        .unwrap()
    }
    /// Message decoding for an RM(1, 7) codeword using Hadamard decoding.
    /// From MacWilliams and Sloane, 1977, Chapter 14
    fn decode_internal(codeword: &Array<u8, Self::InternalCodewordBytesize>) -> u8 {
        // Cannot panic since size is correct
        // Can't directly use ref_from_bytes because of misalignment.
        let c = Array::<u128, Self::M>::read_from_bytes(codeword.as_bytes()).unwrap();

        let transformed = Self::walsh_hadamard(Self::accumulate(&c));
        Self::find_max(&transformed)
    }
}

impl<RM: DuplicatedReedMuller17> InternalCode for RM {}

pub(crate) trait DuplicatedReedMuller17: DuplicatedReedMuller17Param {
    #[inline(always)]
    fn broadcast(bit: bool) -> u128 {
        (bit as u128).wrapping_neg()
    }

    // Step 0. Accumulate every duplicated codeword as one state
    fn accumulate(codeword: &Array<u128, Self::M>) -> ReedMuller17AccumulatedState {
        array::from_fn(|i| codeword.iter().map(|ci| ((ci >> i) & 1) as i16).sum())
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

        tmp[0] -= 64 * Self::M::I16;
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

impl<RM: DuplicatedReedMuller17Param> DuplicatedReedMuller17 for RM {}

type ReedMuller17AccumulatedState = [i16; 128];

#[cfg(test)]
mod test {
    use core::ops::Div;

    use crate::hash::XofState;

    use super::*;
    use hybrid_array::{
        sizes::{U4, U8},
        typenum::Quot,
    };
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    fn test_reed_muller_perfect_channel<RM: InternalCode>() {
        for i in 0..=255 {
            let codeword = RM::encode_internal(&i);

            assert_eq!(i, RM::decode_internal(&codeword));
        }
    }

    fn gen_noise<N: ArraySize + Mul<U8>>(rng: &mut StdRng) -> Array<u8, N>
    where
        Prod<N, U8>: ArraySize + Div<U4>,
        Quot<Prod<N, U8>, U4>: ArraySize,
    {
        let seed: [u8; 8] = rng.random();
        let mut xof = XofState::new(&seed);
        let support: Array<usize, Quot<Prod<N, U8>, U4>> =
            xof.generate_random_support_biased::<Quot<Prod<N, U8>, U4>, Prod<N, U8>>();

        let mut res = Array::default();
        for v in support {
            res[v / 8] |= 1 << (v % 8);
        }
        res
    }

    fn xor_noise<N: ArraySize>(codeword: &mut Array<u8, N>, noise: &Array<u8, N>) {
        codeword.iter_mut().zip(noise).for_each(|(c, n)| *c ^= n);
    }

    fn test_reed_muller_noisy_channel<RM: InternalCode + DuplicatedReedMuller17Param>(seed: u64)
    where
        RM::InternalCodewordBytesize: Mul<U8>,
        Prod<RM::InternalCodewordBytesize, U8>: ArraySize + Div<U4>,
        Quot<Prod<RM::InternalCodewordBytesize, U8>, U4>: ArraySize,
    {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..10000 {
            let message: u8 = rng.random();
            let noise = gen_noise::<RM::InternalCodewordBytesize>(&mut rng);

            let mut codeword = RM::encode_internal(&message);

            xor_noise::<RM::InternalCodewordBytesize>(&mut codeword, &noise);

            assert_eq!(message, RM::decode_internal(&codeword));
        }
    }

    #[test]
    fn test_perfect_hqc1rm() {
        test_reed_muller_perfect_channel::<Hqc1>();
    }

    #[test]
    fn test_perfect_hqc3rm() {
        test_reed_muller_perfect_channel::<Hqc3>();
    }

    #[test]
    fn test_perfect_hqc5rm() {
        test_reed_muller_perfect_channel::<Hqc5>();
    }

    #[test]
    fn test_noisy_hqc1rm() {
        test_reed_muller_noisy_channel::<Hqc1>(1337);
    }

    #[test]
    fn test_noisy_hqc3rm() {
        test_reed_muller_noisy_channel::<Hqc3>(1338);
    }

    #[test]
    fn test_noisy_hqc5rm() {
        test_reed_muller_noisy_channel::<Hqc5>(1339);
    }
}
