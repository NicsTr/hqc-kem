use core::fmt::Debug;
use core::marker::PhantomData;
use ctutils::{CtAssign, CtEq};
use hybrid_array::typenum::Sum;

use hybrid_array::{
    Array, AssocArraySize,
    sizes::{U16, U32, U96},
    typenum::Unsigned,
};

use kem::{
    Decapsulate, Decapsulator, Encapsulate, FromSeed, Generate, Kem, Key, KeyExport, KeyInit,
    KeySizeUser, Seed, TryKeyInit,
};
use rand::{CryptoRng, TryCryptoRng};
use zerocopy::IntoBytes;

use crate::hash::hash_j;
use crate::hash::{XofState, hash_g, hash_h};
use crate::pke::{Ciphertext as PkeCiphertext, DecryptionKey, EncryptionKey, PkeParams};
use crate::polynomial::BinaryPolynomial;
use crate::size_traits::Bytesize;
use crate::{Hqc1, Hqc3, Hqc5};

pub struct Ciphertext<P: PkeParams> {
    pke_ciphertext: PkeCiphertext<P>,
    salt: [u8; 16],
}

impl<P: PkeParams> From<&Array<u8, Sum<Sum<Bytesize<P::NBits>, P::CodewordBytesize>, U16>>>
    for Ciphertext<P>
{
    // TODO: const assert bounds
    fn from(value: &Array<u8, Sum<Sum<Bytesize<P::NBits>, P::CodewordBytesize>, U16>>) -> Self {
        let pke_ciphertext_bytes: &Array<u8, _> = &value
            [..Sum::<Bytesize<P::NBits>, P::CodewordBytesize>::USIZE]
            .try_into()
            .unwrap();
        Self {
            pke_ciphertext: pke_ciphertext_bytes.into(),
            salt: value[Sum::<Bytesize<P::NBits>, P::CodewordBytesize>::USIZE..]
                .try_into()
                .unwrap(),
        }
    }
}

impl<P: PkeParams> From<&Ciphertext<P>>
    for Array<u8, Sum<Sum<Bytesize<P::NBits>, P::CodewordBytesize>, U16>>
{
    // TODO: const assert bounds
    fn from(value: &Ciphertext<P>) -> Self {
        let mut res = Array::default();
        let pke_ciphertext_bytes: Array<u8, _> = (&value.pke_ciphertext).into();
        res[..Sum::<Bytesize<P::NBits>, P::CodewordBytesize>::USIZE]
            .copy_from_slice(&pke_ciphertext_bytes);
        res[Sum::<Bytesize<P::NBits>, P::CodewordBytesize>::USIZE..].copy_from_slice(&value.salt);
        res
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncapsulationKey<P: PkeParams>(EncryptionKey<P>);

// TODO: impl KeySizeUser for DecapsulationKey
impl<P: PkeParams> KeySizeUser for EncapsulationKey<P> {
    type KeySize = Sum<Bytesize<P::NBits>, U32>;
}

impl<P: PkeParams> KeyInit for EncapsulationKey<P> {
    fn new(key: &Key<Self>) -> Self {
        const { assert!(<Key<Self> as AssocArraySize>::Size::USIZE == 32 + Bytesize::<P::NBits>::USIZE) }

        let pke_ek = EncryptionKey {
            // Cannot fail since slices have the same sizes
            ek_seed: key[..32].try_into().unwrap(),
            // Cannot fail since key is of right size (checked by const assert above)
            s: BinaryPolynomial::<P::NBits>::from(&key[32..].try_into().unwrap()),
        };
        Self(pke_ek)
    }
}

impl<P: PkeParams> TryKeyInit for EncapsulationKey<P> {
    fn new(key: &Key<Self>) -> Result<Self, kem::InvalidKey> {
        Ok(<EncapsulationKey<P> as KeyInit>::new(key))
    }
}

impl<P: PkeParams> KeyExport for EncapsulationKey<P> {
    fn to_bytes(&self) -> Key<Self> {
        const { assert!(<Key<Self> as AssocArraySize>::Size::USIZE == 32 + Bytesize::<P::NBits>::USIZE) }
        let mut res = Key::<Self>::default();

        // Cannot fail since slices have the same sizes
        res[..32].copy_from_slice(&self.0.ek_seed);
        let s: Array<u8, Bytesize<P::NBits>> = (&self.0.s).into();
        res[32..].copy_from_slice(&s[..]);

        res
    }
}

impl<P: PkeParams> Encapsulate for EncapsulationKey<P> {
    type Kem = HqcKem<P>;

    fn encapsulate_with_rng<R>(
        &self,
        rng: &mut R,
    ) -> (kem::Ciphertext<Self::Kem>, kem::SharedKey<Self::Kem>)
    where
        R: CryptoRng + ?Sized,
    {
        let mut message = Array::<u8, P::ExternalMessageBytesize>::default();
        let mut salt = [0u8; 16];
        rng.fill_bytes(&mut message);
        rng.fill_bytes(&mut salt);

        let g = hash_g::<P>(&hash_h::<Self::Kem>(self), &message, &salt);

        let (shared_key, theta) = g.split_at(<Self::Kem as Kem>::SharedKeySize::USIZE);

        // Cannot fail (sizes are fixed)
        let ciphertext = Ciphertext {
            pke_ciphertext: self.0.encrypt(&message, theta.try_into().unwrap()),
            salt,
        };

        ((&ciphertext).into(), shared_key.try_into().unwrap())
    }
}

pub struct DecapsulationKey<P: PkeParams> {
    encapsulation_key: EncapsulationKey<P>,
    decryption_key: DecryptionKey,
    rejection_randomness: Array<u8, P::ExternalMessageBytesize>,
    _kem_seed: [u8; 32],
}

impl<P: PkeParams> Decapsulator for DecapsulationKey<P> {
    type Kem = HqcKem<P>;

    fn encapsulation_key(&self) -> &kem::EncapsulationKey<Self::Kem> {
        &self.encapsulation_key
    }
}

impl<P: PkeParams> Decapsulate for DecapsulationKey<P> {
    fn decapsulate(&self, ct: &kem::Ciphertext<Self::Kem>) -> kem::SharedKey<Self::Kem> {
        let ciphertext = Ciphertext::<P>::from(ct);
        let message = self.decryption_key.decrypt(&ciphertext.pke_ciphertext);
        let h = hash_h::<Self::Kem>(self.encapsulation_key());
        let g = hash_g::<P>(&h, &message, &ciphertext.salt);

        let (shared_key, theta) = g.split_at(<Self::Kem as Kem>::SharedKeySize::USIZE);
        let shared_key = shared_key.try_into().unwrap();

        let expected_pke_ciphertext = self
            .encapsulation_key
            .0
            .encrypt(&message, theta.try_into().unwrap());

        // Final key is rejection key if ciphertext and expected ciphertext are not equal.
        let mut final_key = hash_j(&h, &self.rejection_randomness, &ciphertext);
        final_key.ct_assign(
            shared_key,
            ciphertext.pke_ciphertext.ct_eq(&expected_pke_ciphertext),
        );

        Array(final_key)
    }
}

impl<P: PkeParams> Generate for DecapsulationKey<P> {
    fn try_generate_from_rng<R: TryCryptoRng + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        let mut seed = [0u8; 32];
        rng.try_fill_bytes(&mut seed)?;
        let (decapsulation_key, _) = HqcKem::<P>::from_seed(&seed.into());
        Ok(decapsulation_key)
    }
}

impl<P: PkeParams> KeySizeUser for DecapsulationKey<P> {
    type KeySize = Sum<Sum<Bytesize<P::NBits>, U96>, P::ExternalMessageBytesize>;
}

impl<P: PkeParams> KeyExport for DecapsulationKey<P> {
    fn to_bytes(&self) -> Key<Self> {
        const {
            assert!(
                <Key<Self> as AssocArraySize>::Size::USIZE
                    == <kem::EncapsulationKey<<Self as Decapsulator>::Kem> as KeySizeUser>::KeySize::USIZE + 32 + P::ExternalMessageBytesize::USIZE + 32
            )
        }
        let mut res = Key::<Self>::default();

        // Cannot fail since slices have the same sizes
        let encapsulation_key_size =
            <kem::EncapsulationKey<<Self as Decapsulator>::Kem> as KeySizeUser>::KeySize::USIZE;
        res[..encapsulation_key_size].copy_from_slice(&self.encapsulation_key.to_bytes());
        res[encapsulation_key_size..encapsulation_key_size + 32]
            .copy_from_slice(self.decryption_key.as_bytes());
        res[encapsulation_key_size + 32
            ..encapsulation_key_size + 32 + P::ExternalMessageBytesize::USIZE]
            .copy_from_slice(&self.rejection_randomness);
        res[encapsulation_key_size + 32 + P::ExternalMessageBytesize::USIZE..]
            .copy_from_slice(&self._kem_seed);

        res
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct HqcKem<P: PkeParams> {
    _phantom: PhantomData<P>,
}

pub type Hqc1Kem = HqcKem<Hqc1>;
pub type Hqc3Kem = HqcKem<Hqc3>;
pub type Hqc5Kem = HqcKem<Hqc5>;

impl<P: PkeParams> Kem for HqcKem<P> {
    type EncapsulationKey = EncapsulationKey<P>;

    type DecapsulationKey = DecapsulationKey<P>;

    type SharedKeySize = U32;

    type CiphertextSize = Sum<Sum<Bytesize<P::NBits>, P::CodewordBytesize>, U16>;
}

impl<P: PkeParams> FromSeed for HqcKem<P> {
    type SeedSize = U32;

    fn from_seed(seed: &Seed<Self>) -> (kem::DecapsulationKey<Self>, kem::EncapsulationKey<Self>) {
        let mut xof = XofState::new(seed);

        let mut pke_seed = Array::<u8, Self::SeedSize>::default();
        let mut rejection_randomness = Array::default();

        xof.get_bytes(&mut pke_seed);
        xof.get_bytes(&mut rejection_randomness);

        let (encryption_key, decryption_key) = DecryptionKey::keygen(pke_seed.into());

        let encapsulation_key = EncapsulationKey(encryption_key);
        (
            DecapsulationKey {
                encapsulation_key: encapsulation_key.clone(),
                decryption_key,
                rejection_randomness,
                _kem_seed: (*seed).into(),
            },
            encapsulation_key,
        )
    }
}

#[cfg(test)]
mod test {
    use hybrid_array::Array;
    use kem::{Decapsulate, Encapsulate, FromSeed, Kem};
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    use crate::{Hqc3Kem, Hqc5Kem, kem::Hqc1Kem};

    fn test_encaps_decaps<K: Kem + FromSeed>(seed: u64)
    where
        K::DecapsulationKey: Decapsulate,
    {
        let mut rng = StdRng::seed_from_u64(seed);
        let hqc_seed = Array::from_fn(|_| rng.random());
        let (sk, pk) = K::from_seed(&hqc_seed);

        let (ct, ss) = pk.encapsulate_with_rng(&mut rng);

        assert_eq!(sk.decapsulate(&ct), ss);
    }

    #[test]
    fn test_encaps_decaps_hqc1() {
        test_encaps_decaps::<Hqc1Kem>(1337);
    }

    #[test]
    fn test_encaps_decaps_hqc3() {
        test_encaps_decaps::<Hqc3Kem>(1338);
    }

    #[test]
    fn test_encaps_decaps_hqc5() {
        test_encaps_decaps::<Hqc5Kem>(1339);
    }
}
