use std::{convert::Infallible, str::Lines};

use hybrid_array::Array;
use kem::{Encapsulate, FromSeed, Kem, KeyExport};
use rand::{Rng, TryCryptoRng, TryRng};
use sha3::{
    Shake256, Shake256Reader,
    digest::{ExtendableOutput, Update, XofReader},
};

use hqc_kem::{Hqc1Kem, Hqc3Kem, Hqc5Kem};

const HQC_PRNG_DOMAIN_SEPARATOR: u8 = 0;

struct KatCryptoRng(Shake256Reader);

impl KatCryptoRng {
    fn new(kat_seed: &[u8]) -> Self {
        Self(
            Shake256::default()
                .chain(kat_seed)
                .chain(&[HQC_PRNG_DOMAIN_SEPARATOR])
                .finalize_xof(),
        )
    }
}

impl TryRng for KatCryptoRng {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut arr = [0u8; 4];
        self.0.read(&mut arr);

        Ok(u32::from_le_bytes(arr))
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut arr = [0u8; 8];
        self.0.read(&mut arr);

        Ok(u64::from_le_bytes(arr))
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        self.0.read(dst);
        Ok(())
    }
}

impl TryCryptoRng for KatCryptoRng {}

fn test_single_kat<Hqc: Kem + FromSeed>(
    kat_seed: &str,
    expected_pk: &str,
    expected_sk: &str,
    expected_ct: &str,
    expected_ss: &str,
) where
    <Hqc as Kem>::DecapsulationKey: KeyExport,
{
    let kat_seed_bytes = hex::decode(kat_seed).unwrap();

    let mut rng = KatCryptoRng::new(&kat_seed_bytes);

    let mut hqc_seed = Array::default();
    rng.fill_bytes(&mut hqc_seed);
    let (sk, pk) = Hqc::from_seed(&hqc_seed);

    assert_eq!(hex::decode(expected_pk).unwrap()[..], pk.to_bytes()[..]);
    assert_eq!(hex::decode(expected_sk).unwrap()[..], sk.to_bytes()[..]);

    let (ct, ss) = pk.encapsulate_with_rng(&mut rng);

    assert_eq!(hex::decode(expected_ct).unwrap()[..], ct[..]);
    assert_eq!(hex::decode(expected_ss).unwrap()[..], ss[..]);

    // TODO:
    // test decaps
}

fn next_line<'a>(haystack: &mut Lines<'a>, needle: &str) -> &'a str {
    for l in haystack {
        if !l.starts_with(needle) {
            continue;
        }

        return &l[needle.len()..];
    }

    panic!("{needle} not found");
}

fn test_all_kat<Hqc: Kem + FromSeed>(kats_resp: &str)
where
    <Hqc as Kem>::DecapsulationKey: KeyExport,
{
    let seed_for_seeds = hex::decode("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f").unwrap();
    let mut rng = KatCryptoRng::new(&seed_for_seeds);

    let mut kats_resp_lines = kats_resp.lines();
    let kats_name = kats_resp_lines.next().expect("Empty KAT response file.");
    for i in 0..100 {
        println!("KAT ({kats_name}) {i}");

        let mut seed = [0u8; 48];
        rng.fill_bytes(&mut seed);

        let count_l = next_line(&mut kats_resp_lines, "count = ");
        assert_eq!(format!("{i}"), count_l);

        let seed_l = next_line(&mut kats_resp_lines, "seed = ");
        assert_eq!(hex::decode(seed_l).expect("Wrong seed {i}"), seed);

        let pk_l = next_line(&mut kats_resp_lines, "pk = ");
        let sk_l = next_line(&mut kats_resp_lines, "sk = ");
        let ct_l = next_line(&mut kats_resp_lines, "ct = ");
        let ss_l = next_line(&mut kats_resp_lines, "ss = ");

        test_single_kat::<Hqc>(seed_l, pk_l, sk_l, ct_l, ss_l);
    }
}

#[test]
fn test_kat_hqc1() {
    test_all_kat::<Hqc1Kem>(include_str!("kat_hqc1"));
}

#[test]
fn test_kat_hqc3() {
    test_all_kat::<Hqc3Kem>(include_str!("kat_hqc3"));
}

#[test]
fn test_kat_hqc5() {
    test_all_kat::<Hqc5Kem>(include_str!("kat_hqc5"));
}
