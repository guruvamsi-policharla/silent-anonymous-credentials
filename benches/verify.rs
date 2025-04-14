use ark_std::UniformRand;
use criterion::{criterion_group, criterion_main, Criterion};
use silent_anonymous_credentials::{crs::CRS, silent_sps::SK};

type E = ark_bls12_381::Bls12_381;
type G2 = ark_bls12_381::G2Projective;

fn bench_sign(c: &mut Criterion) {
    let n = 1 << 2;
    let crs = CRS::<E>::new(n, &mut ark_std::test_rng());
    let sk = SK::<E>::new(&mut ark_std::test_rng());
    let (vk, hints) = sk.get_pk(&crs, 0);
    let m = G2::rand(&mut ark_std::test_rng());
    let sig = sk.sign(&crs, m, &mut ark_std::test_rng());
    sig.verify(&m, &vk, &crs);
    hints.verify(&vk, &crs);

    c.bench_function("verify", |b| b.iter(|| sig.verify(&m, &vk, &crs)));
}

criterion_group!(benches, bench_sign);
criterion_main!(benches);
