use ark_ec::{pairing::Pairing, ScalarMul};
use ark_ec::{PrimeGroup, VariableBaseMSM};
use ark_ff::{Field, PrimeField};
use ark_poly::Polynomial;
use ark_std::{One, UniformRand, Zero};

use crate::utils::lagrange_poly;

#[derive(Clone, Debug)]
pub struct CRS<E: Pairing> {
    pub ua: [E::G1; 2],
    pub va: [E::G1; 2],
    pub b: [E::G2; 2],
    pub bu: [E::G2; 2],
    pub bv: [E::G2; 2],

    pub n: usize,
    pub powers_of_g: Vec<E::G1Affine>,
    pub powers_of_h: Vec<E::G2Affine>,
    pub a_powers_of_g: Vec<E::G1Affine>,

    // preprocessed lagrange polynomials
    pub li: Vec<E::G1>,
    pub li_minus0: Vec<E::G1>,
    pub li_x: Vec<E::G1>,
    pub li_lj_z: Vec<Vec<E::G1>>,

    pub ali: Vec<E::G1>,
    pub ali_minus0: Vec<E::G1>,
    pub ali_x: Vec<E::G1>,
    pub ali_lj_z: Vec<Vec<E::G1>>,
}

impl<E: Pairing> CRS<E> {
    pub fn new(n: usize) -> Self {
        let mut rng = ark_std::test_rng(); //todo: replace with secure rng
        let a = [E::ScalarField::one(), E::ScalarField::rand(&mut rng)];
        let b_f = [E::ScalarField::one(), E::ScalarField::rand(&mut rng)];
        let u = [
            [
                E::ScalarField::rand(&mut rng),
                E::ScalarField::rand(&mut rng),
            ],
            [
                E::ScalarField::rand(&mut rng),
                E::ScalarField::rand(&mut rng),
            ],
        ];
        let v = [
            [
                E::ScalarField::rand(&mut rng),
                E::ScalarField::rand(&mut rng),
            ],
            [
                E::ScalarField::rand(&mut rng),
                E::ScalarField::rand(&mut rng),
            ],
        ];

        let ua = [
            E::G1::generator() * (u[0][0] * a[0] + u[0][1] * a[1]),
            E::G1::generator() * (u[1][0] * a[0] + u[1][1] * a[1]),
        ];

        let va = [
            E::G1::generator() * (v[0][0] * a[0] + v[0][1] * a[1]),
            E::G1::generator() * (v[1][0] * a[0] + v[1][1] * a[1]),
        ];

        let b = [E::G2::generator() * b_f[0], E::G2::generator() * b_f[1]];

        let bu = [
            E::G2::generator() * (b_f[0] * u[0][0] + b_f[1] * u[1][0]),
            E::G2::generator() * (b_f[0] * u[0][1] + b_f[1] * u[1][1]),
        ];

        let bv = [
            E::G2::generator() * (b_f[0] * v[0][0] + b_f[1] * v[1][0]),
            E::G2::generator() * (b_f[0] * v[0][1] + b_f[1] * v[1][1]),
        ];

        // powers of tau
        let tau = E::ScalarField::rand(&mut rng);

        let mut powers_of_tau = vec![E::ScalarField::one()];

        let mut cur = tau;
        for _ in 0..=n {
            powers_of_tau.push(cur);
            cur *= &tau;
        }

        let powers_of_g = E::G1::generator().batch_mul(&powers_of_tau[0..n + 1]);
        let powers_of_h = E::G2::generator().batch_mul(&powers_of_tau[0..n + 1]);

        let a_powers_of_g = powers_of_g
            .iter()
            .map(|&gtaui| (gtaui * a[1]).into())
            .collect::<Vec<_>>();

        // lagrange powers
        let mut li_evals: Vec<E::ScalarField> = vec![E::ScalarField::zero(); n];
        let mut li_evals_minus0: Vec<E::ScalarField> = vec![E::ScalarField::zero(); n];
        let mut li_evals_x: Vec<E::ScalarField> = vec![E::ScalarField::zero(); n];

        let tau2_inv: <E as Pairing>::ScalarField = (tau * tau).inverse().unwrap();
        for i in 0..n {
            let li = lagrange_poly(n, i);
            li_evals[i] = li.evaluate(&tau);

            li_evals_minus0[i] = (li_evals[i] - li.coeffs[0]) * tau;

            li_evals_x[i] = li_evals_minus0[i] * tau2_inv;
        }

        let z_eval = tau.pow(&[n as u64]) - E::ScalarField::one();
        let z_eval_inv = z_eval.inverse().unwrap();

        let mut li = vec![E::G1::zero(); n];
        let mut ali = vec![E::G1::zero(); n];
        for i in 0..n {
            li[i] = E::G1::generator() * li_evals[i];
            ali[i] = E::G1::generator() * (li_evals[i] * a[1]);
        }

        let mut li_minus0 = vec![E::G1::zero(); n];
        let mut ali_minus0 = vec![E::G1::zero(); n];
        for i in 0..n {
            li_minus0[i] = E::G1::generator() * li_evals_minus0[i];
            ali_minus0[i] = E::G1::generator() * (li_evals_minus0[i] * a[1]);
        }

        let mut li_x = vec![E::G1::zero(); n];
        let mut ali_x = vec![E::G1::zero(); n];
        for i in 0..n {
            li_x[i] = E::G1::generator() * li_evals_x[i];
            ali_x[i] = E::G1::generator() * (li_evals_x[i] * a[1]);
        }

        let mut li_lj_z = vec![vec![E::G1::zero(); n]; n];
        let mut ali_lj_z = vec![vec![E::G1::zero(); n]; n];
        for i in 0..n {
            for j in 0..n {
                li_lj_z[i][j] = if i == j {
                    E::G1::generator() * ((li_evals[i] * li_evals[i] - li_evals[i]) * z_eval_inv)
                } else {
                    E::G1::generator() * (li_evals[i] * li_evals[j] * z_eval_inv)
                };

                ali_lj_z[i][j] = if i == j {
                    E::G1::generator()
                        * ((li_evals[i] * li_evals[i] - li_evals[i]) * z_eval_inv * a[1])
                } else {
                    E::G1::generator() * (li_evals[i] * li_evals[j] * z_eval_inv * a[1])
                };
            }
        }

        // a_lagrange powers

        Self {
            ua,
            va,
            b,
            bu,
            bv,
            n,
            powers_of_g,
            powers_of_h,
            a_powers_of_g,
            li,
            li_minus0,
            li_x,
            li_lj_z,
            ali,
            ali_minus0,
            ali_x,
            ali_lj_z,
        }
    }

    pub fn commit_g1(&self, coeffs: &Vec<E::ScalarField>) -> E::G1 {
        assert!(
            coeffs.len() <= self.powers_of_g.len(),
            "Too many coefficients for the given powers of tau"
        );

        let plain_coeffs = coeffs.iter().map(|c| c.into_bigint()).collect::<Vec<_>>();
        <E::G1 as VariableBaseMSM>::msm_bigint(
            &self.powers_of_g[..coeffs.len()],
            plain_coeffs.as_slice(),
        )
    }

    pub fn commit_g2(&self, coeffs: &Vec<E::ScalarField>) -> E::G2 {
        assert!(
            coeffs.len() <= self.powers_of_g.len(),
            "Too many coefficients for the given powers of tau"
        );

        let plain_coeffs = coeffs.iter().map(|c| c.into_bigint()).collect::<Vec<_>>();
        <E::G2 as VariableBaseMSM>::msm_bigint(
            &self.powers_of_h[..coeffs.len()],
            plain_coeffs.as_slice(),
        )
    }
}
