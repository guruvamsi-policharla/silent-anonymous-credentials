use super::Hints;
use super::{Sig, VK};
use crate::gs08::ProverKey;
use crate::silent_ac::{ShowCRS, Showing};
use crate::{crs::CRS, utils::compute_vanishing_poly};
use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_ec::PrimeGroup;
use ark_ec::VariableBaseMSM;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Polynomial,
    Radix2EvaluationDomain,
};
use ark_std::rand::Rng;
use ark_std::UniformRand;
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

    pub b: E::G2,
    pub avk: [E::G1; 2],
    pub qx: [E::G1; 2],
    pub qz: [E::G1; 2],
    pub bhat: E::G1,
    pub q0: E::G1,
    pub avk_hat: [E::G1; 2],
    pub qxhat: [E::G1; 2],
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
        let n_inv = E::ScalarField::one() / E::ScalarField::from(crs.n as u64);

        let mut bases: Vec<Vec<<E as Pairing>::G1Affine>> = vec![Vec::new(), Vec::new()];
        let mut scalars: Vec<<E as Pairing>::ScalarField> = Vec::new();
        for &i in &parties {
            bases[0].push(self.vk[i].vk[0].into());
            bases[1].push(self.vk[i].vk[1].into());
            scalars.push(b_evals[i]);
        }
        let avk = [
            E::G1::msm(bases[0].as_slice(), scalars.as_slice()).unwrap() * n_inv,
            E::G1::msm(bases[1].as_slice(), scalars.as_slice()).unwrap() * n_inv,
        ];

        let mut bases: Vec<Vec<<E as Pairing>::G1Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(self.hints[i].ka_taun[0].into());
            bases[1].push(self.hints[i].ka_taun[1].into());
        }
        let avk_hat = [
            E::G1::msm(bases[0].as_slice(), scalars.as_slice()).unwrap() * n_inv,
            E::G1::msm(bases[1].as_slice(), scalars.as_slice()).unwrap() * n_inv,
        ];

        // aggregate the individual signatures
        // s1
        let mut bases: Vec<Vec<<E as Pairing>::G2Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(partial_sigs[i].s1[0].into());
            bases[1].push(partial_sigs[i].s1[1].into());
        }
        let s1 = [
            E::G2::msm(bases[0].as_slice(), scalars.as_slice()).unwrap() * n_inv,
            E::G2::msm(bases[1].as_slice(), scalars.as_slice()).unwrap() * n_inv,
        ];

        // s2
        let mut bases: Vec<Vec<<E as Pairing>::G2Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(partial_sigs[i].s2[0].into());
            bases[1].push(partial_sigs[i].s2[1].into());
        }
        let s2 = [
            E::G2::msm(bases[0].as_slice(), scalars.as_slice()).unwrap() * n_inv,
            E::G2::msm(bases[1].as_slice(), scalars.as_slice()).unwrap() * n_inv,
        ];

        // s3
        let mut bases: Vec<Vec<<E as Pairing>::G2Affine>> = vec![Vec::new(), Vec::new()];
        for &i in &parties {
            bases[0].push(partial_sigs[i].s3[0].into());
            bases[1].push(partial_sigs[i].s3[1].into());
        }
        let s3 = [
            E::G2::msm(bases[0].as_slice(), scalars.as_slice()).unwrap() * n_inv,
            E::G2::msm(bases[1].as_slice(), scalars.as_slice()).unwrap() * n_inv,
        ];

        // s4
        // find the first party that signed using selector and use its s4
        let mut s4 = E::G1::zero();
        for i in 0..crs.n {
            if selector[i] {
                s4 = partial_sigs[i].s4;
                break;
            }
        }

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
        let lhs = [-mvk[0], self.avk[0], self.qx[0], self.qz[0]];
        let rhs = [
            self.b,
            E::G2::generator(),
            crs.powers_of_h[1].into(),
            crs.powers_of_h[crs.n] - crs.powers_of_h[0],
        ];
        assert!(E::multi_pairing(lhs, rhs).is_zero());

        // check a2
        let lhs = [-mvk[1], self.avk[1], self.qx[1], self.qz[1]];
        assert!(E::multi_pairing(lhs, rhs).is_zero());

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

    pub fn show(
        &self,
        com_att: E::G2,
        pi: E::G1,
        show_crs: &ShowCRS<E>,
        crs: &CRS<E>,
        pk: &ProverKey<E>,
        rng: &mut impl Rng,
    ) -> Showing<E> {
        let (com_b, r_b) = pk.commit_g2(&self.b, rng);

        let (com_avk_0, r_avk_0) = pk.commit_g1(&self.avk[0], rng);
        let (com_avk_1, r_avk_1) = pk.commit_g1(&self.avk[1], rng);
        let com_avk = [com_avk_0, com_avk_1];
        let r_avk = [r_avk_0, r_avk_1];

        let (com_qx_0, r_qx_0) = pk.commit_g1(&self.qx[0], rng);
        let (com_qx_1, r_qx_1) = pk.commit_g1(&self.qx[1], rng);
        let com_qx = [com_qx_0, com_qx_1];
        let r_qx = [r_qx_0, r_qx_1];

        let (com_qz_0, r_qz_0) = pk.commit_g1(&self.qz[0], rng);
        let (com_qz_1, r_qz_1) = pk.commit_g1(&self.qz[1], rng);
        let com_qz = [com_qz_0, com_qz_1];
        let r_qz = [r_qz_0, r_qz_1];

        let (com_bhat, r_bhat) = pk.commit_g1(&self.bhat, rng);

        let (com_q0, r_q0) = pk.commit_g1(&self.q0, rng);

        let (com_avk_hat_0, r_avk_hat_0) = pk.commit_g1(&self.avk_hat[0], rng);
        let (com_avk_hat_1, r_avk_hat_1) = pk.commit_g1(&self.avk_hat[1], rng);
        let com_avk_hat = [com_avk_hat_0, com_avk_hat_1];
        let r_avk_hat = [r_avk_hat_0, r_avk_hat_1];

        let (com_qxhat_0, r_qxhat_0) = pk.commit_g1(&self.qxhat[0], rng);
        let (com_qxhat_1, r_qxhat_1) = pk.commit_g1(&self.qxhat[1], rng);
        let com_qxhat = [com_qxhat_0, com_qxhat_1];
        let r_qxhat = [r_qxhat_0, r_qxhat_1];

        let (com_com_att, r_com_att) = pk.commit_g2(&com_att, rng);
        let (com_pi, r_pi) = pk.commit_g1(&pi, rng);

        let (com_s1_0, r_s1_0) = pk.commit_g2(&self.s1[0], rng);
        let (com_s1_1, r_s1_1) = pk.commit_g2(&self.s1[1], rng);
        let com_s1 = [com_s1_0, com_s1_1];
        let r_s1 = [r_s1_0, r_s1_1];

        let (com_s2_0, r_s2_0) = pk.commit_g2(&self.s2[0], rng);
        let (com_s2_1, r_s2_1) = pk.commit_g2(&self.s2[1], rng);
        let com_s2 = [com_s2_0, com_s2_1];
        let r_s2 = [r_s2_0, r_s2_1];

        let (com_s3_0, r_s3_0) = pk.commit_g2(&self.s3[0], rng);
        let (com_s3_1, r_s3_1) = pk.commit_g2(&self.s3[1], rng);
        let com_s3 = [com_s3_0, com_s3_1];
        let r_s3 = [r_s3_0, r_s3_1];

        let (com_s4, r_s4) = pk.commit_g1(&self.s4, rng);

        let negg = -E::G1::generator();
        let neg_ga = -(crs.a_powers_of_g[0].into_group());

        //prove that e(s4,s2[0]).e(-g, s3[0]) = 0
        let mut tt = [[E::ScalarField::zero(); 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                tt[i][j] = E::ScalarField::rand(rng);
            }
        }

        let mut rs = [[E::ScalarField::zero(); 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                rs[i][j] = r_s4[i] * r_s2[0][j];
            }
        }

        let mut theta1 = [[E::G1::generator(); 2]; 2];
        let mut pi1 = [[E::G2::generator(); 2]; 2];

        theta1[0][0] = pk.u1[0] * tt[0][0] + pk.u2[0] * tt[1][0];
        theta1[1][0] = pk.u1[0] * tt[0][1] + pk.u2[0] * tt[1][1];
        theta1[0][1] =
            pk.u1[1] * tt[0][0] + pk.u2[1] * tt[1][0] + negg * r_s3[0][0] + self.s4 * r_s2[0][0];
        theta1[1][1] =
            pk.u1[1] * tt[0][1] + pk.u2[1] * tt[1][1] + negg * r_s3[0][1] + self.s4 * r_s2[0][1];

        pi1[0][0] = pk.v1[0] * (rs[0][0] - tt[0][0]) + pk.v2[0] * (rs[0][1] - tt[0][1]);
        pi1[1][0] = pk.v1[0] * (rs[1][0] - tt[1][0]) + pk.v2[0] * (rs[1][1] - tt[1][1]);
        pi1[0][1] = self.s2[0] * r_s4[0]
            + pk.v1[1] * (rs[0][0] - tt[0][0])
            + pk.v2[1] * (rs[0][1] - tt[0][1]);
        pi1[1][1] = self.s2[0] * r_s4[1]
            + pk.v1[1] * (rs[1][0] - tt[1][0])
            + pk.v2[1] * (rs[1][1] - tt[1][1]);

        // prove that e(s4,s2[1]).e(-g, s3[1]) = 0
        let mut tt = [[E::ScalarField::zero(); 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                tt[i][j] = E::ScalarField::rand(rng);
            }
        }

        let mut rs = [[E::ScalarField::zero(); 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                rs[i][j] = r_s4[i] * r_s2[1][j];
            }
        }

        let mut theta2 = [[E::G1::generator(); 2]; 2];
        let mut pi2 = [[E::G2::generator(); 2]; 2];

        let negg = -E::G1::generator();

        theta2[0][0] = pk.u1[0] * tt[0][0] + pk.u2[0] * tt[1][0];
        theta2[1][0] = pk.u1[0] * tt[0][1] + pk.u2[0] * tt[1][1];
        theta2[0][1] =
            pk.u1[1] * tt[0][0] + pk.u2[1] * tt[1][0] + negg * r_s3[1][0] + self.s4 * r_s2[1][0];
        theta2[1][1] =
            pk.u1[1] * tt[0][1] + pk.u2[1] * tt[1][1] + negg * r_s3[1][1] + self.s4 * r_s2[1][1];

        pi2[0][0] = pk.v1[0] * (rs[0][0] - tt[0][0]) + pk.v2[0] * (rs[0][1] - tt[0][1]);
        pi2[1][0] = pk.v1[0] * (rs[1][0] - tt[1][0]) + pk.v2[0] * (rs[1][1] - tt[1][1]);
        pi2[0][1] = self.s2[1] * r_s4[0]
            + pk.v1[1] * (rs[0][0] - tt[0][0])
            + pk.v2[1] * (rs[0][1] - tt[0][1]);
        pi2[1][1] = self.s2[1] * r_s4[1]
            + pk.v1[1] * (rs[1][0] - tt[1][0])
            + pk.v2[1] * (rs[1][1] - tt[1][1]);

        // prove that e(B,K) = show_crs.rhs
        let mut tt = [[E::ScalarField::zero(); 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                tt[i][j] = E::ScalarField::rand(rng);
            }
        }

        let mut theta3 = [[E::G1::generator(); 2]; 2];
        let mut pi3 = [[E::G2::generator(); 2]; 2];

        theta3[0][0] = pk.u1[0] * tt[0][0] + pk.u2[0] * tt[1][0];
        theta3[1][0] = pk.u1[0] * tt[0][1] + pk.u2[0] * tt[1][1];
        theta3[0][1] = pk.u1[1] * tt[0][0]
            + pk.u2[1] * tt[1][0]
            + show_crs.b * r_b[0]
            + show_crs.com_att * r_com_att[0];
        theta3[1][1] = pk.u1[1] * tt[0][1]
            + pk.u2[1] * tt[1][1]
            + show_crs.b * r_b[1]
            + show_crs.com_att * r_com_att[1];

        pi3[0][0] = -(pk.v1[0] * tt[0][0] + pk.v2[0] * tt[0][1]);
        pi3[1][0] = -(pk.v1[0] * tt[1][0] + pk.v2[0] * tt[1][1]);
        pi3[0][1] = E::G2::msm(
            &[
                show_crs.avk[0].into(),
                show_crs.avk[1].into(),
                show_crs.qx[0].into(),
                show_crs.qx[1].into(),
                show_crs.qz[0].into(),
                show_crs.qz[1].into(),
                show_crs.bhat.into(),
                show_crs.q0.into(),
                show_crs.avk_hat[0].into(),
                show_crs.avk_hat[1].into(),
                show_crs.qxhat[0].into(),
                show_crs.qxhat[1].into(),
                show_crs.pi.into(),
                pk.v1[1].into(),
                pk.v2[1].into(),
            ],
            &[
                r_avk[0][0],
                r_avk[1][0],
                r_qx[0][0],
                r_qx[1][0],
                r_qz[0][0],
                r_qz[1][0],
                r_bhat[0],
                r_q0[0],
                r_avk_hat[0][0],
                r_avk_hat[1][0],
                r_qxhat[0][0],
                r_qxhat[1][0],
                r_pi[0],
                -tt[0][0],
                -tt[0][1],
            ],
        )
        .unwrap();

        pi3[1][1] = E::G2::msm(
            &[
                show_crs.avk[0].into(),
                show_crs.avk[1].into(),
                show_crs.qx[0].into(),
                show_crs.qx[1].into(),
                show_crs.qz[0].into(),
                show_crs.qz[1].into(),
                show_crs.bhat.into(),
                show_crs.q0.into(),
                show_crs.avk_hat[0].into(),
                show_crs.avk_hat[1].into(),
                show_crs.qxhat[0].into(),
                show_crs.qxhat[1].into(),
                show_crs.pi.into(),
                pk.v1[1].into(),
                pk.v2[1].into(),
            ],
            &[
                r_avk[0][1],
                r_avk[1][1],
                r_qx[0][1],
                r_qx[1][1],
                r_qz[0][1],
                r_qz[1][1],
                r_bhat[1],
                r_q0[1],
                r_avk_hat[0][1],
                r_avk_hat[1][1],
                r_qxhat[0][1],
                r_qxhat[1][1],
                r_pi[1],
                -tt[1][0],
                -tt[1][1],
            ],
        )
        .unwrap();

        // prove that e(avk[0],1).e(avk[1],com).e(ua[0],s2[0]).e(ua[1],s2[1]).e(va[0],s3[0]).e(va[1],s3[1]).e(-A[0],s1[0]).e(-A[1],s1[1]) = 0
        let mut tt = [[E::ScalarField::zero(); 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                tt[i][j] = E::ScalarField::rand(rng);
            }
        }

        let mut rs = [[E::ScalarField::zero(); 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                rs[i][j] = r_avk[1][i] * r_com_att[j];
            }
        }

        let mut theta4 = [[E::G1::generator(); 2]; 2];
        let mut pi4 = [[E::G2::generator(); 2]; 2];

        theta4[0][0] = pk.u1[0] * tt[0][0] + pk.u2[0] * tt[1][0];
        theta4[1][0] = pk.u1[0] * tt[0][1] + pk.u2[0] * tt[1][1];
        theta4[0][1] = E::G1::msm(
            &[
                pk.u1[1].into(),
                pk.u2[1].into(),
                negg.into(),
                neg_ga.into(),
                crs.ua[0].into(),
                crs.ua[1].into(),
                crs.va[0].into(),
                crs.va[1].into(),
                self.avk[1].into(),
            ],
            &[
                tt[0][0],
                tt[1][0],
                r_s1[0][0],
                r_s1[1][0],
                r_s2[0][0],
                r_s2[1][0],
                r_s3[0][0],
                r_s3[1][0],
                r_com_att[0],
            ],
        )
        .unwrap();

        theta4[1][1] = E::G1::msm(
            &[
                pk.u1[1].into(),
                pk.u2[1].into(),
                negg.into(),
                neg_ga.into(),
                crs.ua[0].into(),
                crs.ua[1].into(),
                crs.va[0].into(),
                crs.va[1].into(),
                self.avk[1].into(),
            ],
            &[
                tt[0][1],
                tt[1][1],
                r_s1[0][1],
                r_s1[1][1],
                r_s2[0][1],
                r_s2[1][1],
                r_s3[0][1],
                r_s3[1][1],
                r_com_att[1],
            ],
        )
        .unwrap();

        pi4[0][0] = pk.v1[0] * (rs[0][0] - tt[0][0]) + pk.v2[0] * (rs[0][1] - tt[0][1]);
        pi4[1][0] = pk.v1[0] * (rs[1][0] - tt[1][0]) + pk.v2[0] * (rs[1][1] - tt[1][1]);
        pi4[0][1] = pk.v1[1] * (rs[0][0] - tt[0][0])
            + pk.v2[1] * (rs[0][1] - tt[0][1])
            + com_att * r_avk[1][0]
            + E::G2::generator() * r_avk[0][0];
        pi4[1][1] = pk.v1[1] * (rs[1][0] - tt[1][0])
            + pk.v2[1] * (rs[1][1] - tt[1][1])
            + com_att * r_avk[1][1]
            + E::G2::generator() * r_avk[0][1];

        Showing {
            com_b,
            com_avk,
            com_qx,
            com_qz,
            com_bhat,
            com_q0,
            com_avk_hat,
            com_qxhat,
            com_com_att,
            com_pi,
            com_s1,
            com_s2,
            com_s3,
            com_s4,
            theta1,
            pi1,
            theta2,
            pi2,
            theta3,
            pi3,
            theta4,
            pi4,
        }
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
    }
}
