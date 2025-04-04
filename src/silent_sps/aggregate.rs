use super::Hints;
use super::{Sig, VK};
use crate::{crs::CRS, utils::compute_vanishing_poly};
use ark_ec::pairing::Pairing;
use ark_ec::PrimeGroup;
use ark_ec::VariableBaseMSM;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Polynomial,
    Radix2EvaluationDomain,
};
use ark_std::{One, Zero};

#[derive(Clone, Debug)]
pub struct AggregateKey<E: Pairing> {
    pub vk: Vec<VK<E>>,
    pub hints: Vec<Hints<E>>,
    pub agg_ka_li_lj_z: Vec<[E::G1; 2]>,
    pub mvk: [E::G1; 2],
}

#[derive(Clone, Debug)]
pub struct AggregateSig<E: Pairing> {
    pub s1: [E::G2; 2],
    pub s2: [E::G2; 2],
    pub s3: [E::G2; 2],
    pub s4: E::G1,

    pub avk: [E::G1; 2],
    pub avk_hat: [E::G1; 2],

    pub b: E::G2,
    pub bhat: E::G1,

    pub qx: [E::G1; 2],
    pub qxhat: [E::G1; 2],
    pub qz: [E::G1; 2],
    pub q0: E::G1,
}

impl<E: Pairing> AggregateKey<E> {
    pub fn new(vk: Vec<VK<E>>, hints: Vec<Hints<E>>) -> Self {
        let n = vk.len();

        let mut mvk = [E::G1::zero(); 2];
        for i in 0..n {
            mvk[0] += hints[i].ka_li[0];
            mvk[1] += hints[i].ka_li[1];
        }

        let mut agg_ka_li_lj_z = vec![];
        for i in 0..n {
            let mut agg_ka_li_lj_zi = [E::G1::zero(); 2];
            for j in 0..n {
                agg_ka_li_lj_zi[0] += hints[j].ka_li_lj_z[i][0];
                agg_ka_li_lj_zi[1] += hints[j].ka_li_lj_z[i][1];
            }
            agg_ka_li_lj_z.push(agg_ka_li_lj_zi);
        }

        AggregateKey {
            vk,
            hints,
            agg_ka_li_lj_z,
            mvk,
        }
    }

    /// the threshold t is set to the the number of true entries in the selector
    /// assumes that s4 across all signatures is the same
    pub fn agg_sig(
        &self,
        partial_sigs: &Vec<Sig<E>>,
        selector: &[bool],
        crs: CRS<E>,
    ) -> AggregateSig<E> {
        let domain = Radix2EvaluationDomain::<E::ScalarField>::new(crs.n).unwrap();
        let domain_elements: Vec<E::ScalarField> = domain.elements().collect();

        // points is where B is set to zero
        // parties is the set of parties who have signed
        let mut points = Vec::new();
        let mut parties: Vec<usize> = Vec::new(); // parties indexed from 0..n-1
        let mut t = 0usize;
        for i in 0..crs.n {
            if selector[i] {
                parties.push(i);
                t += 1;
            } else {
                points.push(domain_elements[i]);
            }
        }

        let b = compute_vanishing_poly(&points);
        let b_evals = domain.fft(&b.coeffs);

        debug_assert!(b.degree() == points.len());
        debug_assert!(b.evaluate(&E::ScalarField::zero()) == E::ScalarField::one());

        // commit to b in g2
        let b_g2: E::G2 = crs.commit_g2(&b.coeffs);

        // q0 = (b-1)/(x)
        let mut bminus1 = b.clone();
        bminus1.coeffs[0] -= E::ScalarField::one();

        debug_assert!(bminus1.evaluate(&E::ScalarField::zero()) == E::ScalarField::zero());

        let q0 = DensePolynomial::from_coefficients_slice(&bminus1.coeffs[1..]);

        let q0_g1 = crs.commit_g1(&q0.coeffs);

        // bhat = x^{t} * b
        // insert t 0s at the beginning of bhat.coeffs
        let mut bhat_coeffs = vec![E::ScalarField::zero(); t];
        bhat_coeffs.append(&mut b.coeffs.clone());
        let bhat = DensePolynomial::from_coefficients_vec(bhat_coeffs);
        debug_assert_eq!(bhat.degree(), crs.n);

        let bhat_g1 = crs.commit_g1(&bhat.coeffs);

        // compute the aggregate verification key
        let mut bases: Vec<Vec<<E as Pairing>::G1Affine>> = vec![Vec::new(), Vec::new()];
        let mut scalars: Vec<<E as Pairing>::ScalarField> = Vec::new();
        for &i in &parties {
            bases[0].push(self.vk[i].vk[0].into());
            bases[1].push(self.vk[i].vk[1].into());
            scalars.push(b_evals[i]);
        }
        let avk = [
            E::G1::msm(bases[0].as_slice(), scalars.as_slice()).unwrap(),
            E::G1::msm(bases[1].as_slice(), scalars.as_slice()).unwrap(),
        ];

        let mut bases: Vec<Vec<<E as Pairing>::G1Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(self.hints[i].ka_taun[0].into());
            bases[1].push(self.hints[i].ka_taun[1].into());
        }
        let avk_hat = [
            E::G1::msm(bases[0].as_slice(), scalars.as_slice()).unwrap(),
            E::G1::msm(bases[1].as_slice(), scalars.as_slice()).unwrap(),
        ];

        // aggregate the individual signatures
        // s1
        let mut bases: Vec<Vec<<E as Pairing>::G2Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(partial_sigs[i].s1[0].into());
            bases[1].push(partial_sigs[i].s1[1].into());
        }
        let s1 = [
            E::G2::msm(bases[0].as_slice(), scalars.as_slice()).unwrap(),
            E::G2::msm(bases[1].as_slice(), scalars.as_slice()).unwrap(),
        ];

        // s2
        let mut bases: Vec<Vec<<E as Pairing>::G2Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(partial_sigs[i].s2[0].into());
            bases[1].push(partial_sigs[i].s2[1].into());
        }
        let s2 = [
            E::G2::msm(bases[0].as_slice(), scalars.as_slice()).unwrap(),
            E::G2::msm(bases[1].as_slice(), scalars.as_slice()).unwrap(),
        ];

        // s3
        let mut bases: Vec<Vec<<E as Pairing>::G2Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(partial_sigs[i].s3[0].into());
            bases[1].push(partial_sigs[i].s3[1].into());
        }
        let s3 = [
            E::G2::msm(bases[0].as_slice(), scalars.as_slice()).unwrap(),
            E::G2::msm(bases[1].as_slice(), scalars.as_slice()).unwrap(),
        ];

        // s4
        let s4 = partial_sigs[0].s4.clone();

        // compute Qx, Qhatx and Qz
        // Qx
        let mut bases: Vec<Vec<<E as Pairing>::G1Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(self.hints[i].ka_li_x[0].into());
            bases[1].push(self.hints[i].ka_li_x[1].into());
        }
        let qx = [
            E::G1::msm(bases[0].as_slice(), scalars.as_slice()).unwrap(),
            E::G1::msm(bases[1].as_slice(), scalars.as_slice()).unwrap(),
        ];

        // Qz
        let mut bases: Vec<Vec<<E as Pairing>::G1Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(self.agg_ka_li_lj_z[i][0].into());
            bases[1].push(self.agg_ka_li_lj_z[i][1].into());
        }
        let qz = [
            E::G1::msm(bases[0].as_slice(), scalars.as_slice()).unwrap(),
            E::G1::msm(bases[1].as_slice(), scalars.as_slice()).unwrap(),
        ];

        // Qxhat
        let mut bases: Vec<Vec<<E as Pairing>::G1Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(self.hints[i].ka_li_minus0[0].into());
            bases[1].push(self.hints[i].ka_li_minus0[1].into());
        }
        let qxhat = [
            E::G1::msm(bases[0].as_slice(), scalars.as_slice()).unwrap(),
            E::G1::msm(bases[1].as_slice(), scalars.as_slice()).unwrap(),
        ];

        AggregateSig {
            s1,
            s2,
            s3,
            s4,

            avk,
            avk_hat,

            b: b_g2,
            bhat: bhat_g1,

            qx,
            qxhat,
            qz,
            q0: q0_g1,
        }
    }
}

impl<E: Pairing> AggregateSig<E> {
    pub fn verify(&self, m: E::G2, t: usize, mvk: &[E::G1; 2], crs: &CRS<E>) {
        let negg = -E::G1::generator();
        let negh = -E::G2::generator();

        // check a1
        let lhs = E::pairing(mvk[0], self.b);
        let rhs = E::pairing(self.avk[0], E::G2::generator())
            + E::pairing(self.qx[0], crs.powers_of_h[1])
            + E::pairing(self.qz[0], crs.powers_of_h[crs.n] - crs.powers_of_h[0]);

        assert!(lhs == rhs);

        // let lhs = [-mvk[0], self.avk[0], self.qx[0], self.qz[0]];
        // let rhs = [
        //     self.b,
        //     E::G2::generator(),
        //     crs.powers_of_h[1].into(),
        //     crs.powers_of_h[crs.n] - crs.powers_of_h[0],
        // ];
        // assert!(E::multi_pairing(lhs, rhs).is_zero());

        // check a2
        // let lhs = [-mvk[1], self.avk[1], self.qx[1], self.qz[1]];
        // assert!(E::multi_pairing(lhs, rhs).is_zero());

        // check b
        let lhs = [crs.powers_of_g[t].into(), self.bhat];
        let rhs = [self.b, negh];
        assert!(E::multi_pairing(lhs, rhs).is_zero());

        // check c
        let lhs = [negg, self.q0, E::G1::generator()];
        let rhs = [self.b, crs.powers_of_h[1].into(), E::G2::generator()];
        assert!(E::multi_pairing(lhs, rhs).is_zero());

        // check d
        let lhs = [self.avk_hat[0], self.avk[0]];
        let rhs = [negh, crs.powers_of_h[crs.n].into()];
        assert!(E::multi_pairing(lhs, rhs).is_zero());

        let lhs = [self.avk_hat[1], self.avk[1]];
        let rhs = [negh, crs.powers_of_h[crs.n].into()];
        assert!(E::multi_pairing(lhs, rhs).is_zero());

        // check e
        let lhs = [self.qx[0], self.qxhat[0]];
        let rhs: [<E as Pairing>::G2; 2] = [crs.powers_of_h[2].into(), negh];
        assert!(E::multi_pairing(lhs, rhs).is_zero());

        let lhs = [self.qx[1], self.qxhat[1]];
        let rhs = [crs.powers_of_h[2].into(), negh];
        assert!(E::multi_pairing(lhs, rhs).is_zero());

        // check f, g
        let sps_sig = Sig::<E> {
            s1: self.s1,
            s2: self.s2,
            s3: self.s3,
            s4: self.s4,
        };
        let agg_vk = VK::<E> { vk: self.avk };

        sps_sig.verify(&m, &agg_vk, &crs);
    }
}

#[cfg(test)]
mod tests {
    use crate::crs::CRS;
    use crate::silent_sps::Sig;
    use crate::silent_sps::SK;

    use ark_bls12_381::Bls12_381 as E;
    use ark_bls12_381::G1Projective as G1;
    use ark_bls12_381::G2Projective as G2;
    use ark_std::{UniformRand, Zero};

    use super::AggregateKey;

    #[test]
    fn test_aggregation() {
        let n = 1 << 5;
        let t = n / 2;
        let crs = CRS::<E>::new(n);
        let mut sk = Vec::new();
        let mut vk = Vec::new();
        let mut hints = Vec::new();
        let mut partial_sigs = Vec::new();

        let m = G2::rand(&mut ark_std::test_rng());
        for i in 0..n {
            sk.push(SK::<E>::new());
            let (vki, hinti) = sk[i].get_pk(&crs, i);
            vk.push(vki);
            hints.push(hinti);
        }

        let mut selector = vec![false; n];

        for i in 0..t {
            selector[i] = true;
        }

        for i in 0..n {
            if selector[i] {
                partial_sigs.push(sk[i].sign(&crs, m));
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
    }
}
