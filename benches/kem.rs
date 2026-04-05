use criterion::{Criterion, criterion_group, criterion_main};
use hqc_kem::{Hqc1Kem, Hqc3Kem, Hqc5Kem};
use hybrid_array::Array;
use kem::{Decapsulate, Encapsulate, FromSeed};
use rand::Rng;

fn bench_keygen(c: &mut Criterion) {
    let mut rng = rand::rng();
    let mut hqc_seed = Array::default();
    rng.fill_bytes(&mut hqc_seed);

    c.bench_function("HQC-1: key generation", |b| {
        b.iter(|| Hqc1Kem::from_seed(&hqc_seed))
    });
    c.bench_function("HQC-3: key generation", |b| {
        b.iter(|| Hqc3Kem::from_seed(&hqc_seed))
    });
    c.bench_function("HQC-5: key generation", |b| {
        b.iter(|| Hqc5Kem::from_seed(&hqc_seed))
    });
}

fn bench_encaps(c: &mut Criterion) {
    let mut rng = rand::rng();
    let mut hqc_seed = Array::default();
    rng.fill_bytes(&mut hqc_seed);

    let (_, ek1) = Hqc1Kem::from_seed(&hqc_seed);
    let (_, ek3) = Hqc3Kem::from_seed(&hqc_seed);
    let (_, ek5) = Hqc5Kem::from_seed(&hqc_seed);

    c.bench_function("HQC-1: encapsulate", |b| {
        b.iter(|| ek1.encapsulate_with_rng(&mut rng))
    });
    c.bench_function("HQC-3: encapsulate", |b| {
        b.iter(|| ek3.encapsulate_with_rng(&mut rng))
    });
    c.bench_function("HQC-5: encapsulate", |b| {
        b.iter(|| ek5.encapsulate_with_rng(&mut rng))
    });
}

fn bench_decaps(c: &mut Criterion) {
    let mut rng = rand::rng();
    let mut hqc_seed = Array::default();
    rng.fill_bytes(&mut hqc_seed);

    let (dk1, ek1) = Hqc1Kem::from_seed(&hqc_seed);
    let (dk3, ek3) = Hqc3Kem::from_seed(&hqc_seed);
    let (dk5, ek5) = Hqc5Kem::from_seed(&hqc_seed);

    let (ct1, _) = ek1.encapsulate_with_rng(&mut rng);
    let (ct3, _) = ek3.encapsulate_with_rng(&mut rng);
    let (ct5, _) = ek5.encapsulate_with_rng(&mut rng);

    c.bench_function("HQC-1: decapsulate", |b| b.iter(|| dk1.decapsulate(&ct1)));
    c.bench_function("HQC-3: decapsulate", |b| b.iter(|| dk3.decapsulate(&ct3)));
    c.bench_function("HQC-5: decapsulate", |b| b.iter(|| dk5.decapsulate(&ct5)));
}

criterion_group!(benches, bench_keygen, bench_encaps, bench_decaps);
criterion_main!(benches);
