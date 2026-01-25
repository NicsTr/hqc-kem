use crypto_common::OutputSizeUser;
use ctutils::{Choice, CtAssign, CtEq};
use hybrid_array::{Array, ArraySize};
use sha3::{
    Digest, Sha3_256, Sha3_512, Shake256, Shake256Reader,
    digest::{ExtendableOutput, Update, XofReader},
};

const XOF_DOMAIN_SEPARATOR: u8 = 1;
const G_DOMAIN_SEPARATOR: u8 = 0;
const H_DOMAIN_SEPARATOR: u8 = 1;
const I_DOMAIN_SEPARATOR: u8 = 2;
const J_DOMAIN_SEPARATOR: u8 = 3;

#[inline]
fn hash_helper<H: Digest>(
    input: &[u8],
    domain_separator: u8,
) -> Array<u8, <H as OutputSizeUser>::OutputSize>
where
    H::OutputSize: ArraySize,
{
    let h = H::new_with_prefix(input)
        .chain_update([domain_separator])
        .finalize();
    // Cannot fail since H::OutputSize is exactly the size of the returned Array
    Array::try_from(&h[..]).unwrap()
}

pub(crate) fn hash_g(input: &[u8]) -> Array<u8, <Sha3_512 as OutputSizeUser>::OutputSize> {
    hash_helper::<Sha3_512>(input, G_DOMAIN_SEPARATOR)
}

pub(crate) fn hash_h(input: &[u8]) -> Array<u8, <Sha3_256 as OutputSizeUser>::OutputSize> {
    hash_helper::<Sha3_256>(input, H_DOMAIN_SEPARATOR)
}

pub(crate) fn hash_i(input: &[u8]) -> Array<u8, <Sha3_512 as OutputSizeUser>::OutputSize> {
    hash_helper::<Sha3_512>(input, I_DOMAIN_SEPARATOR)
}

pub(crate) fn hash_j(input: &[u8]) -> Array<u8, <Sha3_256 as OutputSizeUser>::OutputSize> {
    hash_helper::<Sha3_256>(input, J_DOMAIN_SEPARATOR)
}

pub(crate) struct XofState(Shake256Reader);

impl XofState {
    pub(crate) fn new<N: ArraySize>(seed: &Array<u8, N>) -> Self {
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

    /// Generate an (almost) uniformly random u32 between 0 and `max`.
    ///
    /// The generation is not uniform but its bias is negligible
    /// for the target security levels.
    fn get_randint(&mut self, max: u32) -> u32 {
        let mut rand_buf = [0u8; 4];
        self.get_bytes(&mut rand_buf);
        ((u32::from_le_bytes(rand_buf) as u64 * max as u64) >> 32) as u32
    }

    /// Generate a random support of weight `W` in constant time using this XOF.
    ///
    /// According to https://eprint.iacr.org/2021/1631, the support is not uniform
    /// but its bias is negligible for the target security levels.
    ///
    /// Based on HQC reference implementation.
    pub(crate) fn generate_random_support<W: ArraySize, N: ArraySize>(
        &mut self,
    ) -> Array<usize, W> {
        // Initialize result
        let mut res = Array::from_fn(|i| i + self.get_randint(N::U32 - (i as u32)) as usize);

        // When a collision occured, replace the value by the index of collision.
        for i in (0..W::USIZE).rev() {
            let mut collision = Choice::FALSE;

            for j in (i + 1)..W::USIZE {
                collision |= res[i].ct_eq(&res[j]);
            }

            res[i].ct_assign(&i, collision);
        }

        res
    }

    /// Sample a fixed weight `u8` array where the non-zero values are ones.
    pub(crate) fn sample_fixed_weight<W: ArraySize, N: ArraySize>(&mut self) -> Array<u8, N> {
        let mut res = Array::default();

        for v in self.generate_random_support::<W, N>() {
            res[v] = 1;
        }

        res
    }
}
