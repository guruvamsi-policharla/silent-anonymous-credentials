use ark_ec::AffineRepr;
use ark_ec::{pairing::Pairing, PrimeGroup};
use ark_ff::{Field, PrimeField};
use ark_poly::Polynomial;
use ark_std::{One, UniformRand, Zero};

use crate::crs::PowersOfTau;
use crate::utils::{hash_to_bytes, lagrange_poly};

#[derive(Clone, Debug)]
pub struct CRS<E: Pairing> {
    pub ua: [E::G1; 2],
    pub va: [E::G1; 2],
    pub b: [E::G2; 2],
    pub bu: [E::G2; 2],
    pub bv: [E::G2; 2],

    pub n: usize,
    pub powers_of_tau: PowersOfTau<E>,
    pub a_powers_of_tau: Vec<E::G1>,

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

#[derive(Clone, Debug)]
pub struct SK<E: Pairing> {
    k: [[E::ScalarField; 2]; 2],
}

#[derive(Clone, Debug)]
pub struct VK<E: Pairing> {
    pub vk: [E::G1; 2],

    pub a0_neg: E::G1,
    pub a1_neg: E::G1,

    pub g1_gen_neg: E::G1,

    pub ua: [E::G1; 2],
    pub va: [E::G1; 2],

    // hints
    pub id: usize, // position in the committee of n parties

    pub ka_li: [E::G1; 2],
    pub ka_li_minus0: [E::G1; 2],
    pub ka_li_lj_z: Vec<[E::G1; 2]>,
    pub ka_li_x: [E::G1; 2],
}

#[derive(Clone, Debug)]
pub struct Sig<E: Pairing> {
    pub s1: [E::G2; 2],
    pub s2: [E::G2; 2],
    pub s3: [E::G2; 2],
    pub s4: E::G1,
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

        let powers_of_tau = PowersOfTau::<E>::setup(n, tau);

        let a_powers_of_tau = powers_of_tau
            .powers_of_g
            .iter()
            .map(|&gtaui| gtaui * a[1])
            .collect::<Vec<_>>();

        // lagrange powers
        let mut li_evals: Vec<E::ScalarField> = vec![E::ScalarField::zero(); n];
        let mut li_evals_minus0: Vec<E::ScalarField> = vec![E::ScalarField::zero(); n];
        let mut li_evals_x: Vec<E::ScalarField> = vec![E::ScalarField::zero(); n];

        let tau_inv = tau.inverse().unwrap();
        for i in 0..n {
            let li = lagrange_poly(n, i);
            li_evals[i] = li.evaluate(&tau);

            li_evals_minus0[i] = li_evals[i] - li.coeffs[0];

            li_evals_x[i] = li_evals_minus0[i] * tau_inv;
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
            powers_of_tau,
            a_powers_of_tau,
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
}

impl<E: Pairing> SK<E> {
    pub fn new() -> Self {
        let mut rng = ark_std::test_rng(); //todo: replace with secure rng
        let k = [
            [
                E::ScalarField::rand(&mut rng),
                E::ScalarField::rand(&mut rng),
            ],
            [
                E::ScalarField::rand(&mut rng),
                E::ScalarField::rand(&mut rng),
            ],
        ];
        Self { k }
    }

    pub fn get_pk(&self, crs: &CRS<E>, id: usize) -> VK<E> {
        let ka0 =
            crs.powers_of_tau.powers_of_g[0] * self.k[0][0] + crs.a_powers_of_tau[0] * self.k[0][1];
        let ka1 =
            crs.powers_of_tau.powers_of_g[0] * self.k[1][0] + crs.a_powers_of_tau[0] * self.k[1][1];

        let vk = [ka0, ka1];

        let a0_neg = -crs.powers_of_tau.powers_of_g[0].into_group();
        let a1_neg = -crs.a_powers_of_tau[0];

        let g1_gen_neg = -E::G1::generator();

        let ka_li = [
            crs.li[id] * self.k[0][0] + crs.ali[id] * self.k[0][1],
            crs.li[id] * self.k[1][0] + crs.ali[id] * self.k[1][1],
        ];

        let ka_li_minus0 = [
            crs.li_minus0[id] * self.k[0][0] + crs.ali_minus0[id] * self.k[0][1],
            crs.li_minus0[id] * self.k[1][0] + crs.ali_minus0[id] * self.k[1][1],
        ];

        let ka_li_x = [
            crs.li_x[id] * self.k[0][0] + crs.ali_x[id] * self.k[0][1],
            crs.li_x[id] * self.k[1][0] + crs.ali_x[id] * self.k[1][1],
        ];

        let mut ka_li_lj_z = vec![];
        for j in 0..crs.n {
            ka_li_lj_z.push([
                crs.li_lj_z[id][j] * self.k[0][0] + crs.ali_lj_z[id][j] * self.k[0][1],
                crs.li_lj_z[id][j] * self.k[1][0] + crs.ali_lj_z[id][j] * self.k[1][1],
            ]);
        }

        VK {
            vk,
            a0_neg,
            a1_neg,
            g1_gen_neg,
            ua: crs.ua.clone(),
            va: crs.va.clone(),
            id,
            ka_li,
            ka_li_minus0,
            ka_li_lj_z,
            ka_li_x,
        }
    }

    pub fn sign(&self, crs: &CRS<E>, m: E::G2) -> Sig<E> {
        let h = <E::ScalarField as PrimeField>::from_le_bytes_mod_order(&hash_to_bytes(m));
        let rng = &mut ark_std::test_rng(); //todo: replace with secure rng
        let r = E::ScalarField::rand(rng);

        let s1 = [
            E::G2::generator() * self.k[0][0]
                + m * self.k[1][0]
                + crs.bu[0] * r
                + crs.bv[0] * (r * h),
            E::G2::generator() * self.k[0][1]
                + m * self.k[1][1]
                + crs.bu[1] * r
                + crs.bv[1] * (r * h),
        ];

        let s2 = [crs.b[0] * r, crs.b[1] * r];

        let s3 = [crs.b[0] * (r * h), crs.b[1] * (r * h)];

        let s4 = E::G1::generator() * h;

        Sig { s1, s2, s3, s4 }
    }
}

impl<E: Pairing> VK<E> {
    pub fn verify(&self, m: &E::G2, sig: &Sig<E>) {
        // check 1
        let lhs = [
            self.a0_neg,
            self.a1_neg,
            self.vk[0],
            self.vk[1],
            self.ua[0],
            self.ua[1],
            self.va[0],
            self.va[1],
        ];

        let rhs = [
            sig.s1[0],
            sig.s1[1],
            E::G2::generator(),
            m.clone(),
            sig.s2[0],
            sig.s2[1],
            sig.s3[0],
            sig.s3[1],
        ];

        let should_be_zero = E::multi_miller_loop(lhs, rhs);
        let should_be_zero = E::final_exponentiation(should_be_zero).unwrap();

        assert!(should_be_zero.is_zero());

        // check 2
        let lhs = [sig.s4, self.g1_gen_neg];
        let rhs = [sig.s2[0], sig.s3[0]];

        let should_be_zero = E::multi_miller_loop(lhs, rhs);
        let should_be_zero = E::final_exponentiation(should_be_zero).unwrap();
        assert!(should_be_zero.is_zero());

        // check 3
        let rhs = [sig.s2[1], sig.s3[1]];

        let should_be_zero = E::multi_miller_loop(lhs, rhs);
        let should_be_zero = E::final_exponentiation(should_be_zero).unwrap();
        assert!(should_be_zero.is_zero());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381 as E;
    // use ark_bls12_381::Fr as F;
    use ark_bls12_381::G2Projective as G2;

    #[test]
    fn test_crs() {
        let n = 1 << 5;
        let crs = CRS::<E>::new(n);
        assert_eq!(crs.n, n);
        assert_eq!(crs.ua.len(), 2);
        assert_eq!(crs.va.len(), 2);
        assert_eq!(crs.b.len(), 2);
        assert_eq!(crs.bu.len(), 2);
        assert_eq!(crs.bv.len(), 2);
        assert_eq!(crs.powers_of_tau.powers_of_g.len(), n + 1);
        assert_eq!(crs.a_powers_of_tau.len(), n + 1);
    }

    #[test]
    fn test_signing() {
        let n = 1 << 5;
        let crs = CRS::<E>::new(n);
        let sk = SK::<E>::new();
        let vk = sk.get_pk(&crs, 0);
        let m = G2::rand(&mut ark_std::test_rng());
        let sig = sk.sign(&crs, m);
        vk.verify(&m, &sig);
    }

    #[test]
    fn test_aggregation() {
        let n = 1 << 5;
        let crs = CRS::<E>::new(n);
        let mut sk = Vec::new();
        let mut vk = Vec::new();
        for i in 0..n {
            sk.push(SK::<E>::new());
            vk.push(sk[i].get_pk(&crs, i));
        }
    }
}
