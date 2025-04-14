use ark_std::UniformRand;
use ark_std::Zero;
use criterion::BenchmarkId;
use criterion::{criterion_group, criterion_main, Criterion};
use silent_anonymous_credentials::crs::CRS;
use silent_anonymous_credentials::silent_sps::aggregate::AggregateKey;
use silent_anonymous_credentials::silent_sps::Sig;
use silent_anonymous_credentials::silent_sps::SK;

type E = ark_bls12_381::Bls12_381;
type G1 = ark_bls12_381::G1Projective;
type G2 = ark_bls12_381::G2Projective;

fn bench_aggregate(c: &mut Criterion) {
    let mut group = c.benchmark_group("agg_sig");

    use rayon::prelude::*;
    rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build_global()
        .unwrap();

    let sizes = [1 << 6, 1 << 8, 1 << 10]; // Different sizes of n
    for &n in &sizes {
        let t = n / 2;
        let crs = CRS::<E>::new(n, &mut ark_std::test_rng());
        let mut sk = Vec::new();
        for _ in 0..n {
            sk.push(SK::<E>::new(&mut ark_std::test_rng()));
        }

        let m = G2::rand(&mut ark_std::test_rng());

        let rayon_pool = rayon::ThreadPoolBuilder::new()
            .num_threads(num_cpus::get() / 2)
            .build()
            .unwrap();

        let (vk, hints): (Vec<_>, Vec<_>) = rayon_pool.install(|| {
            (0..n)
                .into_par_iter()
                .map(|i| {
                    let (vki, hinti) = sk[i].get_pk(&crs, i);
                    hinti.verify(&vki, &crs);
                    (vki, hinti)
                })
                .unzip()
        });

        drop(rayon_pool);

        let mut selector = vec![false; n];

        for i in 1..t + 1 {
            selector[i] = true;
        }

        let mut partial_sigs = Vec::new();
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
        let agg_sig = agg_key.agg_sig(&partial_sigs, &selector, &crs);

        // verify
        agg_sig.verify(m, t, &agg_key.mvk, &crs);

        group.bench_with_input(
            BenchmarkId::from_parameter(n),
            &(partial_sigs, selector, crs),
            |b, inp| b.iter(|| agg_key.agg_sig(&inp.0, &inp.1, &inp.2)),
        );
    }
}

criterion_group!(benches, bench_aggregate);
criterion_main!(benches);
