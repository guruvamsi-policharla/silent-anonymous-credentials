use ark_std::UniformRand;
use ark_std::Zero;
use criterion::{criterion_group, criterion_main, Criterion};
use silent_sps::silent_sps::aggregate::AggregateKey;
use silent_sps::silent_sps::Sig;
use silent_sps::{crs::CRS, silent_sps::SK};

type E = ark_bls12_381::Bls12_381;
type G1 = ark_bls12_381::G1Projective;
type G2 = ark_bls12_381::G2Projective;

fn bench_aggregate(c: &mut Criterion) {
    let n = 1 << 4;
    let t = n / 2;
    let crs = CRS::<E>::new(n, &mut ark_std::test_rng());
    let mut sk = Vec::new();
    let mut vk = Vec::new();
    let mut hints = Vec::new();
    let mut partial_sigs = Vec::new();

    let m = G2::rand(&mut ark_std::test_rng());
    for i in 0..n {
        sk.push(SK::<E>::new(&mut ark_std::test_rng()));
        let (vki, hinti) = sk[i].get_pk(&crs, i);
        hinti.verify(&vki, &crs);
        vk.push(vki);
        hints.push(hinti);
    }

    let mut selector = vec![false; n];

    for i in 1..t + 1 {
        selector[i] = true;
    }

    for i in 0..n {
        if selector[i] {
            partial_sigs.push(sk[i].sign(&crs, m, &mut ark_std::test_rng()));
        } else {
            partial_sigs.push(Sig {
                s1: [G2::zero(), G2::zero()],
                s2: [G2::zero(), G2::zero()],
                s3: [G2::zero(), G2::zero()],
                s4: G1::zero(),
            });
        }
    }

    for i in 0..n {
        if selector[i] {
            partial_sigs[i].verify(&m, &vk[i], &crs);
        }
    }

    let agg_key = AggregateKey::<E>::new(vk.clone(), hints.clone());
    let agg_sig = agg_key.agg_sig(&partial_sigs, &selector, crs.clone());

    // verify
    agg_sig.verify(m, t, &agg_key.mvk, &crs);

    c.bench_function("agg_sig", |b| {
        b.iter(|| agg_key.agg_sig(&partial_sigs, &selector, crs.clone()))
    });
}

criterion_group!(benches, bench_aggregate);
criterion_main!(benches);
