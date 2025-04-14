use ark_poly::univariate::DensePolynomial;
use ark_poly::DenseUVPolynomial;
use ark_poly::EvaluationDomain;
use ark_poly::Radix2EvaluationDomain;
use ark_std::UniformRand;
use ark_std::Zero;
use criterion::{criterion_group, criterion_main, Criterion};
use silent_anonymous_credentials::crs::CRS;
use silent_anonymous_credentials::gs08;
use silent_anonymous_credentials::silent_ac::ShowCRS;
use silent_anonymous_credentials::silent_sps::aggregate::AggregateKey;
use silent_anonymous_credentials::silent_sps::Sig;
use silent_anonymous_credentials::silent_sps::SK;

// type E = ark_bls12_381::Bls12_381;
// type G1 = ark_bls12_381::G1Projective;
// type G2 = ark_bls12_381::G2Projective;
// type F = ark_bls12_381::Fr;

type E = ark_bn254::Bn254;
type G1 = ark_bn254::G1Projective;
type G2 = ark_bn254::G2Projective;
type F = ark_bn254::Fr;

fn bench_show_verify(c: &mut Criterion) {
    let rng = &mut ark_std::test_rng();
    let n = 1 << 4;
    let t = n / 2;
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let crs = CRS::<E>::new(n, rng);
    let mut sk = Vec::new();
    let mut vk = Vec::new();
    let mut hints = Vec::new();
    let mut partial_sigs = Vec::new();

    // sample n random attributes and commit to them
    let att_coeffs = (0..n).map(|_| F::rand(rng)).collect::<Vec<_>>();

    let att_poly = DensePolynomial::from_coefficients_slice(&att_coeffs);
    let att = att_poly.evaluate_over_domain(domain);

    let com = crs.commit_g2(&att_coeffs);
    let pi = crs.compute_opening_proof(&att_coeffs, &domain.element(1));

    for i in 0..n {
        sk.push(SK::<E>::new(rng));
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
            partial_sigs.push(sk[i].sign(&crs, com, rng));
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
            partial_sigs[i].verify(&com, &vk[i], &crs);
        }
    }

    let agg_key = AggregateKey::<E>::new(vk.clone(), hints.clone());
    let agg_sig = agg_key.agg_sig(&partial_sigs, &selector, &crs);

    // verify
    agg_sig.verify(com, t, &agg_key.mvk, &crs);

    let show_crs = ShowCRS::<E>::new(rng, agg_key, crs.clone(), t, domain.element(1), att[1]);

    let pk = gs08::ProverKey::<E>::setup(rng);
    let showing = agg_sig.show(com, pi, &show_crs, &crs, &pk, rng);
    showing.verify(&show_crs, &crs, &pk);

    c.bench_function("show_verify", |b| {
        b.iter(|| showing.verify(&show_crs, &crs, &pk))
    });
}

criterion_group!(benches, bench_show_verify);
criterion_main!(benches);
