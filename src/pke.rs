use core::ops::{Add, Div, Sub};

use hybrid_array::{
    ArraySize,
    sizes::{U1, U64, U66, U75, U100, U114, U131, U149, U17669, U35851, U57637},
    typenum::{Diff, Quot, Sum, Unsigned},
};
use zerocopy::IntoBytes;

use crate::{
    code::{Code, HQC1Code},
    polynomial::BinaryPolynomial,
    utils::{XofState, hash_i},
};

pub(crate) struct PkeEncryptionKey<P: Pke> {
    ek_seed: [u8; 32],
    s: BinaryPolynomial<P::NBits>,
}

pub(crate) struct PkeDecryptionKey([u8; 32]);

pub(crate) struct PkeCiphertext<P: Pke> {
    u: BinaryPolynomial<P::NBits>,
    v: <P::HqcCode as Code>::Codeword,
}

pub(crate) trait Pke: Sized
where
    Self::NBits: Sub<U1> + Unsigned,
    Diff<Self::NBits, U1>: Div<U64>,
    Quot<Diff<Self::NBits, U1>, U64>: Add<U1>,
    Sum<Quot<Diff<Self::NBits, U1>, U64>, U1>: ArraySize,
{
    type NBits: Unsigned;
    type W: ArraySize;
    type We: ArraySize;
    type HqcCode: Code;

    fn keygen(seed: [u8; 32]) -> (PkeEncryptionKey<Self>, PkeDecryptionKey) {
        // Generate encryption and decryption seeds
        let expanded_seed: [u8; 64] = hash_i(&seed);
        let dk_seed: [u8; 32] = expanded_seed[..32]
            .try_into()
            .expect("size invariant violated");
        let ek_seed: [u8; 32] = expanded_seed[32..64]
            .try_into()
            .expect("size invariant violated");

        // Generate decryption key
        let mut xof_x_y = XofState::new(&dk_seed);
        let y = xof_x_y.sample_fixed_weight_vect_rejection::<Self::W, Self::NBits>();
        let x = xof_x_y.sample_fixed_weight_vect_rejection::<Self::W, Self::NBits>();

        // Generate encryption key
        let mut xof_h = XofState::new(&ek_seed);
        let h = xof_h.sample_vect();
        let s = x + h * &y;

        (PkeEncryptionKey { ek_seed, s }, PkeDecryptionKey(dk_seed))
    }

    fn encrypt(
        ek: PkeEncryptionKey<Self>,
        message: <Self::HqcCode as Code>::Message,
        theta: [u8; 32],
    ) -> PkeCiphertext<Self> {
        let mut xof_h = XofState::new(&ek.ek_seed);
        let h = xof_h.sample_vect();

        let mut xof_encrypt = XofState::new(&theta);
        let r2 = xof_encrypt.sample_fixed_weight_vect_biased::<Self::We, Self::NBits>();
        let e = xof_encrypt.sample_fixed_weight_vect_biased::<Self::We, Self::NBits>();
        let r1 = xof_encrypt.sample_fixed_weight_vect_biased::<Self::We, Self::NBits>();

        let u = r1 + h * &r2;
        let mut v = Self::HqcCode::encode_once(&message);

        let mask = ek.s * &r2 + e;

        for (vi, mi) in v
            .as_mut_bytes()
            .iter_mut()
            .zip(mask.as_bytes_truncated::<<Self::HqcCode as Code>::NBytes>())
        {
            *vi ^= mi;
        }

        // todo!("tests");
        PkeCiphertext { u, v }
    }

    fn decrypt(
        dk: PkeDecryptionKey,
        ciphertext: PkeCiphertext<Self>,
    ) -> <Self::HqcCode as Code>::Message {
        let mut xof_x_y = XofState::new(&dk.0);
        let y = xof_x_y.sample_fixed_weight_vect_rejection::<Self::W, Self::NBits>();

        let demask = ciphertext.u * &y;

        let mut v = ciphertext.v;

        for (vi, mi) in v
            .as_mut_bytes()
            .iter_mut()
            .zip(demask.as_bytes_truncated::<<Self::HqcCode as Code>::NBytes>())
        {
            *vi ^= mi;
        }

        // todo!("tests");
        Self::HqcCode::decode_once(&v)
    }
}

impl<P: Pke> PkeEncryptionKey<P> {}

pub(crate) struct HQC1Pke;
pub(crate) struct HQC3Pke;
pub(crate) struct HQC5Pke;

impl Pke for HQC1Pke {
    type NBits = U17669;
    type W = U66;
    type We = U75;
    type HqcCode = HQC1Code;
}

impl Pke for HQC3Pke {
    type NBits = U35851;
    type W = U100;
    type We = U114;
    type HqcCode = HQC1Code;
}

impl Pke for HQC5Pke {
    type NBits = U57637;
    type W = U131;
    type We = U149;
    type HqcCode = HQC1Code;
}

#[cfg(test)]
mod test {
    use hybrid_array::Array;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use zerocopy::IntoBytes;

    use crate::{
        code::Code,
        pke::{HQC1Pke, HQC3Pke, HQC5Pke, Pke},
    };

    fn test_encrypt_decrypt<P: Pke>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);
        let seed: [u8; 32] = rng.random();
        let theta: [u8; 32] = rng.random();

        let (ek, dk) = P::keygen(seed);
        let msg_raw = Array::<u8, <P::HqcCode as Code>::KBytes>::default();
        let c = P::encrypt(ek, msg_raw.clone().into(), theta);

        let msg_decrypted = P::decrypt(dk, c);
        assert_eq!(msg_raw.as_bytes(), msg_decrypted.as_bytes());
    }

    #[test]
    fn test_encrypt_decrypt_hqc1() {
        test_encrypt_decrypt::<HQC1Pke>(1337);
    }

    #[test]
    fn test_encrypt_decrypt_hqc3() {
        test_encrypt_decrypt::<HQC3Pke>(1338);
    }

    #[test]
    fn test_encrypt_decrypt_hqc5() {
        test_encrypt_decrypt::<HQC5Pke>(1339);
    }
}
