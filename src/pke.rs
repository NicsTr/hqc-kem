use core::fmt::Debug;
use core::ops::{Add, Mul};

use ctutils::{Choice, CtEq};
use hybrid_array::{
    Array, ArraySize,
    sizes::{U2, U8, U16, U32, U64, U66, U75, U96, U100, U114, U131, U149, U17669, U35851, U57637},
    typenum::{Prod, Sum, Unsigned},
};
use kem::KeySizeUser;
use zerocopy::{Immutable, IntoBytes};

use crate::{
    Hqc1, Hqc3, Hqc5,
    code::{Code, CodeParams},
    hash::{XofState, hash_i},
    polynomial::BinaryPolynomial,
    size_traits::{Bytesize, Octobytesize, WordsizeFromBitsize},
};

#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub(crate) struct EncryptionKey<P: PkeParams> {
    pub(crate) ek_seed: [u8; 32],
    pub(crate) s: BinaryPolynomial<P::NBits>,
}

impl<P: PkeParams> KeySizeUser for EncryptionKey<P> {
    type KeySize = Sum<Bytesize<P::NBits>, U32>;
}

impl<P: PkeParams> EncryptionKey<P> {
    pub(crate) fn encrypt(
        &self,
        message: &Array<u8, P::ExternalMessageBytesize>,
        theta: &[u8; 32],
    ) -> Ciphertext<P> {
        let mut xof_h = XofState::new(&self.ek_seed);
        let mut h_r2 = xof_h.sample_vect::<P>();

        let mut xof_encrypt = XofState::new(theta);
        let mut r2 = xof_encrypt.sample_fixed_weight_vect_biased::<P>();
        h_r2 *= &mut r2;

        let mut r2_s = r2;
        // We need mutability of self.s for in-place multiplication, so we do a big copy here...
        r2_s *= &mut self.s.clone();

        let e = xof_encrypt.sample_fixed_weight_vect_biased::<P>();
        let mask = r2_s + e;
        let r1 = xof_encrypt.sample_fixed_weight_vect_biased::<P>();

        let u = r1 + h_r2;
        let mut v = <P as Code>::encode(message);

        for (vi, mi) in v
            .as_mut_bytes()
            .iter_mut()
            .zip(mask.as_bytes_truncated::<<P as CodeParams>::CodewordBytesize>())
        {
            *vi ^= mi;
        }

        Ciphertext { u, v }
    }
}

#[derive(IntoBytes, Immutable)]
#[repr(transparent)]
pub(crate) struct DecryptionKey([u8; 32]);

impl DecryptionKey {
    pub(crate) fn keygen<P: PkeParams>(seed: [u8; 32]) -> (EncryptionKey<P>, Self) {
        // Generate encryption and decryption seeds
        let expanded_seed: [u8; 64] = hash_i(&seed);
        let dk_seed: [u8; 32] = expanded_seed[..32]
            .try_into()
            .expect("size invariant violated");
        let ek_seed: [u8; 32] = expanded_seed[32..64]
            .try_into()
            .expect("size invariant violated");

        // Generate encryption key
        let mut xof_h = XofState::new(&ek_seed);
        let mut h_y = xof_h.sample_vect::<P>();

        // Generate decryption key
        let mut xof_x_y = XofState::new(&dk_seed);
        let mut y = xof_x_y.sample_fixed_weight_vect_rejection::<P>();
        h_y *= &mut y;

        let x = xof_x_y.sample_fixed_weight_vect_rejection::<P>();

        (
            EncryptionKey {
                ek_seed,
                s: x + h_y,
            },
            Self(dk_seed),
        )
    }

    pub(crate) fn decrypt<P: PkeParams>(
        &self,
        ciphertext: &Ciphertext<P>,
    ) -> Array<u8, P::ExternalMessageBytesize> {
        let mut xof_x_y = XofState::new(&self.0);
        let mut y_u = xof_x_y.sample_fixed_weight_vect_rejection::<P>();

        // We need mutability of u for in-place multiplication, so we do a big clone here...
        y_u *= &mut ciphertext.u.clone();
        let demask = y_u.as_mut_bytes_truncated::<<P as CodeParams>::CodewordBytesize>();

        for (demaski, vi) in demask.iter_mut().zip(ciphertext.v.as_bytes()) {
            *demaski ^= vi;
        }

        // Ugly, but this is done to avoid copying data around...
        let c: &mut Array<_, _> = demask.try_into().unwrap();

        P::decode(c)
    }
}

pub(crate) struct Ciphertext<P: PkeParams> {
    pub(crate) u: BinaryPolynomial<P::NBits>,
    pub(crate) v: Array<u8, <P as CodeParams>::CodewordBytesize>,
}

impl<P: PkeParams> From<&Ciphertext<P>>
    for Array<u8, Sum<Bytesize<P::NBits>, P::CodewordBytesize>>
{
    fn from(value: &Ciphertext<P>) -> Self {
        //TODO: add const assert
        let mut res = Array::default();
        let u_bytes: Array<u8, _> = (&value.u).into();

        res[..Bytesize::<P::NBits>::USIZE].copy_from_slice(&u_bytes);
        res[Bytesize::<P::NBits>::USIZE..].copy_from_slice(value.v.as_bytes());
        res
    }
}

impl<P: PkeParams> From<&Array<u8, Sum<Bytesize<P::NBits>, <P as CodeParams>::CodewordBytesize>>>
    for Ciphertext<P>
{
    fn from(
        value: &Array<u8, Sum<Bytesize<P::NBits>, <P as CodeParams>::CodewordBytesize>>,
    ) -> Self {
        //TODO: add const assert
        // Cannot fail since sizes are right by definition of type
        let u_bytes: Array<u8, _> = value[..Bytesize::<P::NBits>::USIZE].try_into().unwrap();
        let v_bytes: Array<u8, _> = value[Bytesize::<P::NBits>::USIZE..].try_into().unwrap();

        Self {
            u: (&u_bytes).into(),
            v: v_bytes,
        }
    }
}

impl<P: PkeParams> CtEq for Ciphertext<P> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.u.ct_eq(&other.u) & self.v.ct_eq(&other.v)
    }
}

pub trait PkeParams:
    CodeParams + Sized + PartialEq + Eq + Debug + Ord + Default + Copy + Send + Sync + 'static
where
    Bytesize<Self::NBits>: Add<U32> + Add<Self::CodewordBytesize> + Add<U96>,
    Sum<Bytesize<Self::NBits>, U32>: ArraySize, // Encryption/Encapsulation key
    Sum<Bytesize<Self::NBits>, U96>: Add<Self::ExternalMessageBytesize>,
    Sum<Sum<Bytesize<Self::NBits>, U96>, Self::ExternalMessageBytesize>: ArraySize, // Decapsulation key
    Sum<Bytesize<Self::NBits>, Self::CodewordBytesize>: ArraySize + Add<U16>,
    Sum<Sum<Bytesize<Self::NBits>, Self::CodewordBytesize>, U16>: ArraySize,
    // Karatsuba buffer
    Octobytesize<Self::NBits>: Mul<U2>,
    Prod<Octobytesize<Self::NBits>, U2>: ArraySize,
{
    type NBits: PartialEq + Eq + Debug + WordsizeFromBitsize<U64> + WordsizeFromBitsize<U8>;
    type W: ArraySize;
    type We: ArraySize;
}

impl PkeParams for Hqc1 {
    type NBits = U17669;
    type W = U66;
    type We = U75;
}

impl PkeParams for Hqc3 {
    type NBits = U35851;
    type W = U100;
    type We = U114;
}

impl PkeParams for Hqc5 {
    type NBits = U57637;
    type W = U131;
    type We = U149;
}

#[cfg(test)]
mod test {
    use hybrid_array::Array;
    use rand::{RngExt, SeedableRng, rngs::StdRng};
    use zerocopy::IntoBytes;

    use crate::pke::{DecryptionKey, Hqc1, Hqc3, Hqc5, PkeParams};

    fn test_encrypt_decrypt<P: PkeParams>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let seed: [u8; 32] = rng.random();
        let theta: [u8; 32] = rng.random();

        let (ek, dk) = DecryptionKey::keygen::<P>(seed);
        let msg_raw = Array::<u8, P::ExternalMessageBytesize>::default();
        let c = ek.encrypt(&msg_raw.clone().into(), &theta);

        let msg_decrypted = dk.decrypt(&c);
        assert_eq!(msg_raw.as_bytes(), msg_decrypted.as_bytes());
    }

    #[test]
    fn test_encrypt_decrypt_hqc1() {
        test_encrypt_decrypt::<Hqc1>(1337);
    }

    #[test]
    fn test_encrypt_decrypt_hqc3() {
        test_encrypt_decrypt::<Hqc3>(1338);
    }

    #[test]
    fn test_encrypt_decrypt_hqc5() {
        test_encrypt_decrypt::<Hqc5>(1339);
    }
}
