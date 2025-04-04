use ark_ec::{pairing::Pairing, AffineRepr, PrimeGroup};
use ark_ff::PrimeField;
use ark_std::{UniformRand, Zero};

use crate::{crs::CRS, utils::hash_to_bytes};

pub mod aggregate;

#[derive(Clone, Debug)]
pub struct SK<E: Pairing> {
    k: [[E::ScalarField; 2]; 2],
}

#[derive(Clone, Debug)]
pub struct VK<E: Pairing> {
    pub vk: [E::G1; 2],
}

#[derive(Clone, Debug)]
pub struct Hints<E: Pairing> {
    pub id: usize, // position in the committee of n parties
    pub ka_li: [E::G1; 2],
    pub ka_li_minus0: [E::G1; 2],
    pub ka_li_lj_z: Vec<[E::G1; 2]>,
    pub ka_li_x: [E::G1; 2],
    pub ka_taun: [E::G1; 2],
}

#[derive(Clone, Debug)]
pub struct Sig<E: Pairing> {
    pub s1: [E::G2; 2],
    pub s2: [E::G2; 2],
    pub s3: [E::G2; 2],
    pub s4: E::G1,
}

impl<E: Pairing> Hints<E> {
    pub fn verify(&self, vk: &VK<E>, crs: &CRS<E>) {
        let lhs = E::pairing(self.ka_li[0], E::G2::generator());
        let rhs = E::pairing(vk.vk[0], crs.li_g2[self.id]);
        assert!(lhs == rhs);

        let lhs = E::pairing(self.ka_li[1], E::G2::generator());
        let rhs = E::pairing(vk.vk[1], crs.li_g2[self.id]);
        assert!(lhs == rhs);

        ////
        let lhs = E::pairing(self.ka_li_minus0[0], E::G2::generator());
        let rhs = E::pairing(vk.vk[0], crs.li_minus0_g2[self.id]);
        assert!(lhs == rhs);

        let lhs = E::pairing(self.ka_li_minus0[1], E::G2::generator());
        let rhs = E::pairing(vk.vk[1], crs.li_minus0_g2[self.id]);
        assert!(lhs == rhs);

        ////
        let lhs = E::pairing(self.ka_li_x[0], E::G2::generator());
        let rhs = E::pairing(vk.vk[0], crs.li_x_g2[self.id]);
        assert!(lhs == rhs);

        let lhs = E::pairing(self.ka_li_x[1], E::G2::generator());
        let rhs = E::pairing(vk.vk[1], crs.li_x_g2[self.id]);
        assert!(lhs == rhs);

        ////
        for j in 0..crs.n {
            let lhs = E::pairing(self.ka_li_lj_z[j][0], E::G2::generator());
            let rhs = E::pairing(vk.vk[0], crs.li_lj_z_g2[self.id][j]);
            assert!(lhs == rhs);

            let lhs = E::pairing(self.ka_li_lj_z[j][1], E::G2::generator());
            let rhs = E::pairing(vk.vk[1], crs.li_lj_z_g2[self.id][j]);
            assert!(lhs == rhs);
        }

        ////
        let lhs = E::pairing(self.ka_taun[0], E::G2::generator());
        let rhs = E::pairing(vk.vk[0], crs.powers_of_h[crs.n]);
        assert!(lhs == rhs);

        let lhs = E::pairing(self.ka_taun[1], E::G2::generator());
        let rhs = E::pairing(vk.vk[1], crs.powers_of_h[crs.n]);
        assert!(lhs == rhs);
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

    pub fn get_pk(&self, crs: &CRS<E>, id: usize) -> (VK<E>, Hints<E>) {
        let ka0 = crs.powers_of_g[0] * self.k[0][0] + crs.a_powers_of_g[0] * self.k[0][1];
        let ka1 = crs.powers_of_g[0] * self.k[1][0] + crs.a_powers_of_g[0] * self.k[1][1];

        let vk = [ka0, ka1];

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

        let ka_taun = [
            crs.powers_of_g[crs.n] * self.k[0][0] + crs.a_powers_of_g[crs.n] * self.k[0][1],
            crs.powers_of_g[crs.n] * self.k[1][0] + crs.a_powers_of_g[crs.n] * self.k[1][1],
        ];

        (
            VK { vk },
            Hints {
                id,
                ka_li,
                ka_li_minus0,
                ka_li_lj_z,
                ka_li_x,
                ka_taun,
            },
        )
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

impl<E: Pairing> Sig<E> {
    pub fn verify(&self, m: &E::G2, vk: &VK<E>, crs: &CRS<E>) {
        // check 1
        let lhs = [
            -crs.powers_of_g[0].into_group(),
            -crs.a_powers_of_g[0].into_group(),
            vk.vk[0],
            vk.vk[1],
            crs.ua[0],
            crs.ua[1],
            crs.va[0],
            crs.va[1],
        ];

        let rhs = [
            self.s1[0],
            self.s1[1],
            E::G2::generator(),
            m.clone(),
            self.s2[0],
            self.s2[1],
            self.s3[0],
            self.s3[1],
        ];

        assert!(E::multi_pairing(lhs, rhs).is_zero());

        // check 2
        let lhs = [self.s4, -E::G1::generator()];
        let rhs = [self.s2[0], self.s3[0]];

        assert!(E::multi_pairing(lhs, rhs).is_zero());

        // check 3
        let rhs = [self.s2[1], self.s3[1]];

        assert!(E::multi_pairing(lhs, rhs).is_zero());
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
        assert_eq!(crs.powers_of_g.len(), n + 1);
        assert_eq!(crs.powers_of_h.len(), n + 1);
        assert_eq!(crs.a_powers_of_g.len(), n + 1);
    }

    #[test]
    fn test_signing() {
        let n = 1 << 5;
        let crs = CRS::<E>::new(n);
        let sk = SK::<E>::new();
        let (vk, hints) = sk.get_pk(&crs, 0);
        let m = G2::rand(&mut ark_std::test_rng());
        let sig = sk.sign(&crs, m);
        sig.verify(&m, &vk, &crs);

        hints.verify(&vk, &crs);
    }

    #[test]
    fn test_aggregation() {
        let n = 1 << 5;
        let crs = CRS::<E>::new(n);

        let sk1 = SK::<E>::new();
        let (vk1, _hints1) = sk1.get_pk(&crs, 0);

        let sk2 = SK::<E>::new();
        let (vk2, _hints2) = sk2.get_pk(&crs, 0);

        let m = G2::rand(&mut ark_std::test_rng());

        let sig1 = sk1.sign(&crs, m);
        let sig2 = sk2.sign(&crs, m);

        sig1.verify(&m, &vk1, &crs);
        sig2.verify(&m, &vk2, &crs);

        let sig = Sig::<E> {
            s1: [sig1.s1[0] + sig2.s1[0], sig1.s1[1] + sig2.s1[1]],
            s2: [sig1.s2[0] + sig2.s2[0], sig1.s2[1] + sig2.s2[1]],
            s3: [sig1.s3[0] + sig2.s3[0], sig1.s3[1] + sig2.s3[1]],
            s4: sig1.s4,
        };

        let vk = VK::<E> {
            vk: [vk1.vk[0] + vk2.vk[0], vk1.vk[1] + vk2.vk[1]],
        };

        sig.verify(&m, &vk, &crs);
    }
}
