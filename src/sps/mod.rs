use ark_ec::AffineRepr;
use ark_ec::{pairing::Pairing, PrimeGroup};
use ark_ff::PrimeField;
use ark_std::{One, UniformRand, Zero};

use crate::crs::PowersOfTau;
use crate::utils::hash_to_bytes;

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

        let tau = E::ScalarField::rand(&mut rng);
        let powers_of_tau = PowersOfTau::<E>::setup(n, tau);

        let a_powers_of_tau = powers_of_tau
            .powers_of_g
            .iter()
            .map(|&gtaui| gtaui * a[1])
            .collect::<Vec<_>>();

        Self {
            ua,
            va,
            b,
            bu,
            bv,
            n,
            powers_of_tau,
            a_powers_of_tau,
        }
    }
}

#[derive(Clone, Debug)]
pub struct SK<E: Pairing> {
    k: [[E::ScalarField; 2]; 2],
}

#[derive(Clone, Debug)]
pub struct VK<E: Pairing> {
    pub vk: [E::G1; 2],
}

#[derive(Clone, Debug)]
pub struct Sig<E: Pairing> {
    pub s1: [E::G2; 2],
    pub s2: [E::G2; 2],
    pub s3: [E::G2; 2],
    pub s4: E::G1,
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
    pub fn new(crs: &CRS<E>, sk: &SK<E>) -> Self {
        let vk = [
            crs.powers_of_tau.powers_of_g[0] * sk.k[0][0] + crs.a_powers_of_tau[0] * sk.k[0][1],
            crs.powers_of_tau.powers_of_g[0] * sk.k[1][0] + crs.a_powers_of_tau[0] * sk.k[1][1],
        ];
        Self { vk }
    }

    pub fn verify(&self, m: &E::G2, sig: &Sig<E>, crs: &CRS<E>) {
        // check 1
        let lhs = [
            -(crs.powers_of_tau.powers_of_g[0].into_group()),
            -crs.a_powers_of_tau[0],
            self.vk[0],
            self.vk[1],
            crs.ua[0],
            crs.ua[1],
            crs.va[0],
            crs.va[1],
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
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381 as E;
    use ark_bls12_381::G1Projective as G1;
    use ark_bls12_381::G2Projective as G2;

    #[test]
    fn test_crs() {
        let n = 10;
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
        let n = 10;
        let crs = CRS::<E>::new(n);
        let sk = SK::<E>::new();
        let vk = VK::new(&crs, &sk);
        let m = G2::rand(&mut ark_std::test_rng());

        let sig = sk.sign(&crs, m);

        vk.verify(&m, &sig, &crs);
    }
}
