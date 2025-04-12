use crate::crs::CRS;
use crate::gs08;
use crate::silent_sps::aggregate::AggregateKey;
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::AffineRepr;
use ark_ec::PrimeGroup;
use ark_std::rand::Rng;
use ark_std::UniformRand;
use ark_std::Zero;

#[derive(Clone, Debug)]
pub struct ShowCRS<E: Pairing> {
    pub t: usize,
    pub x: E::ScalarField,
    pub y: E::ScalarField,

    pub avk: [E::G2; 2],
    pub avk_hat: [E::G2; 2],

    pub b: E::G1,
    pub bhat: E::G2,

    pub qx: [E::G2; 2],
    pub qxhat: [E::G2; 2],
    pub qz: [E::G2; 2],
    pub q0: E::G2,

    pub com_att: E::G1,
    pub pi: E::G2,

    pub rhs: PairingOutput<E>,
}

// b = s_0 \cdot \bfvk[0] + s_1 \cdot \bfvk[1] + s_2 \cdot [\tau^{t}]_2 + s_3 \cdot [1]_2
// avk[0] = -(s_0 \cdot [1]_1 + s_4 \cdot [\tau^N])
// avk[1] = -(s_1 \cdot [1]_1 + s_5 \cdot [\tau^N])
// qx[0] = -(s_0 \cdot [\tau]_1 + s_6 \cdot [\tau^2]_1)
// qx[1] = -(s_1 \cdot [\tau]_1 + s_7 \cdot [\tau^2]_1)
// qz[0] = -(s_0 \cdot \left[\tau^N - 1\right]_1)
// qz[1] = -(s_1 \cdot \left[\tau^N - 1\right]_1)
// bhat = -(s_2 \cdot [1]_1)
// q0 = -(s_3 \cdot [\tau]_1)
// avk_hat[0] = s_4 \cdot [1]_1
// avk_hat[1] = s_5 \cdot [1]_1
// qxhat[0] = s_6 \cdot [1]_1
// qxhat[1] = s_7 \cdot [1]_1
// com = s_9 \cdot [1]_1
// pi = -(s_8 \cdot [\tau - x^*]_2)

impl<E: Pairing> ShowCRS<E> {
    pub fn new(
        rng: &mut impl Rng,
        agg_key: AggregateKey<E>,
        crs: CRS<E>,
        t: usize,
        x: E::ScalarField,
        y: E::ScalarField,
    ) -> Self {
        // sample a random vector of field elements of size 8
        let s = (0..11)
            .map(|_| E::ScalarField::rand(rng))
            .collect::<Vec<_>>();

        // s[0] = E::ScalarField::zero();
        // s[1] = E::ScalarField::zero();
        // s[2] = E::ScalarField::zero();
        // s[3] = E::ScalarField::zero();
        // s[4] = E::ScalarField::zero();
        // s[5] = E::ScalarField::zero();
        // s[6] = E::ScalarField::zero();
        // s[7] = E::ScalarField::zero();
        // s[8] = E::ScalarField::zero();
        // s[9] = E::ScalarField::zero();
        // s[10] = E::ScalarField::zero();

        let b = (agg_key.mvk[0] * s[0])
            + (agg_key.mvk[1] * s[1])
            + (crs.powers_of_g[t] * s[2])
            + (E::G1::generator() * s[3]);

        let avk = [
            -((E::G2::generator() * s[0]) + (crs.powers_of_h[crs.n] * s[4])),
            -((E::G2::generator() * s[1]) + (crs.powers_of_h[crs.n] * s[5])),
        ];

        let qx = [
            -((crs.powers_of_h[1] * s[0]) + (crs.powers_of_h[2] * s[6])),
            -((crs.powers_of_h[1] * s[1]) + (crs.powers_of_h[2] * s[7])),
        ];

        let qz = [
            -((crs.powers_of_h[crs.n] - E::G2::generator()) * s[0]),
            -((crs.powers_of_h[crs.n] - E::G2::generator()) * s[1]),
        ];

        let bhat = -(E::G2::generator() * s[2]);

        let q0 = -(crs.powers_of_h[1] * s[3]);

        let avk_hat = [(E::G2::generator() * s[4]), (E::G2::generator() * s[5])];

        let qxhat = [(E::G2::generator() * s[6]), (E::G2::generator() * s[7])];

        let com_att = E::G1::generator() * s[9];

        let pi = -((crs.powers_of_h[1] - (E::G2::generator() * x)) * s[9]);

        let rhs = E::pairing(E::G1::generator() * (s[9] * y), E::G2::generator())
            + E::pairing(E::G1::generator() * s[3], E::G2::generator());

        ShowCRS {
            t,
            x,
            y,
            avk,
            avk_hat,
            b,
            bhat,
            qx,
            qxhat,
            qz,
            q0,
            com_att,
            pi,
            rhs,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Showing<E: Pairing> {
    pub com_b: [E::G2; 2],
    pub com_avk: [[E::G1; 2]; 2],
    pub com_qx: [[E::G1; 2]; 2],
    pub com_qz: [[E::G1; 2]; 2],
    pub com_bhat: [E::G1; 2],
    pub com_q0: [E::G1; 2],
    pub com_avk_hat: [[E::G1; 2]; 2],
    pub com_qxhat: [[E::G1; 2]; 2],
    pub com_com_att: [E::G2; 2],
    pub com_pi: [E::G1; 2],

    pub com_s1: [[E::G2; 2]; 2],
    pub com_s2: [[E::G2; 2]; 2],
    pub com_s3: [[E::G2; 2]; 2],
    pub com_s4: [E::G1; 2],

    // proofs
    pub theta1: [[E::G1; 2]; 2],
    pub pi1: [[E::G2; 2]; 2],

    pub theta2: [[E::G1; 2]; 2],
    pub pi2: [[E::G2; 2]; 2],

    pub theta3: [[E::G1; 2]; 2],
    pub pi3: [[E::G2; 2]; 2],

    pub theta4: [[E::G1; 2]; 2],
    pub pi4: [[E::G2; 2]; 2],
}

impl<E: Pairing> Showing<E> {
    pub fn verify(&self, show_crs: &ShowCRS<E>, crs: &CRS<E>, pk: &gs08::ProverKey<E>) {
        let negg = -E::G1::generator();
        let neg_ga = -(crs.a_powers_of_g[0].into_group());

        // constraint 1
        // check 1
        let lhs = E::pairing(self.com_s4[0], self.com_s2[0][0]);
        let rhs = E::pairing(self.theta1[0][0], pk.v1[0])
            + E::pairing(self.theta1[1][0], pk.v2[0])
            + E::pairing(pk.u1[0], self.pi1[0][0])
            + E::pairing(pk.u2[0], self.pi1[1][0]);
        assert_eq!(lhs, rhs);

        // check 2
        let lhs = E::pairing(self.com_s4[0], self.com_s2[0][1]);
        let rhs = E::pairing(pk.u1[0], self.pi1[0][1])
            + E::pairing(pk.u2[0], self.pi1[1][1])
            + E::pairing(self.theta1[0][0], pk.v1[1])
            + E::pairing(self.theta1[1][0], pk.v2[1]);
        assert_eq!(lhs, rhs);

        // check 3
        let lhs =
            E::pairing(negg, self.com_s3[0][0]) + E::pairing(self.com_s4[1], self.com_s2[0][0]);
        let rhs = E::pairing(self.theta1[0][1], pk.v1[0])
            + E::pairing(self.theta1[1][1], pk.v2[0])
            + E::pairing(pk.u1[1], self.pi1[0][0])
            + E::pairing(pk.u2[1], self.pi1[1][0]);
        assert_eq!(lhs, rhs);

        // check 4
        let lhs =
            E::pairing(negg, self.com_s3[0][1]) + E::pairing(self.com_s4[1], self.com_s2[0][1]);
        let rhs = E::pairing(pk.u1[1], self.pi1[0][1])
            + E::pairing(pk.u2[1], self.pi1[1][1])
            + E::pairing(self.theta1[0][1], pk.v1[1])
            + E::pairing(self.theta1[1][1], pk.v2[1]);
        assert_eq!(lhs, rhs);

        // constraint 2
        // check 1
        let lhs = E::pairing(self.com_s4[0], self.com_s2[1][0]);
        let rhs = E::pairing(self.theta2[0][0], pk.v1[0])
            + E::pairing(self.theta2[1][0], pk.v2[0])
            + E::pairing(pk.u1[0], self.pi2[0][0])
            + E::pairing(pk.u2[0], self.pi2[1][0]);
        assert_eq!(lhs, rhs);

        // check 2
        let lhs = E::pairing(self.com_s4[0], self.com_s2[1][1]);
        let rhs = E::pairing(pk.u1[0], self.pi2[0][1])
            + E::pairing(pk.u2[0], self.pi2[1][1])
            + E::pairing(self.theta2[0][0], pk.v1[1])
            + E::pairing(self.theta2[1][0], pk.v2[1]);
        assert_eq!(lhs, rhs);

        // check 3
        let lhs =
            E::pairing(negg, self.com_s3[1][0]) + E::pairing(self.com_s4[1], self.com_s2[1][0]);
        let rhs = E::pairing(self.theta2[0][1], pk.v1[0])
            + E::pairing(self.theta2[1][1], pk.v2[0])
            + E::pairing(pk.u1[1], self.pi2[0][0])
            + E::pairing(pk.u2[1], self.pi2[1][0]);
        assert_eq!(lhs, rhs);

        // check 4
        let lhs =
            E::pairing(negg, self.com_s3[1][1]) + E::pairing(self.com_s4[1], self.com_s2[1][1]);
        let rhs = E::pairing(pk.u1[1], self.pi2[0][1])
            + E::pairing(pk.u2[1], self.pi2[1][1])
            + E::pairing(self.theta2[0][1], pk.v1[1])
            + E::pairing(self.theta2[1][1], pk.v2[1]);
        assert_eq!(lhs, rhs);

        // constraint 3
        // check 1
        let rhs = E::pairing(self.theta3[0][0], pk.v1[0])
            + E::pairing(self.theta3[1][0], pk.v2[0])
            + E::pairing(pk.u1[0], self.pi3[0][0])
            + E::pairing(pk.u2[0], self.pi3[1][0]);
        assert!(rhs.is_zero());

        // check 2
        let lhs = E::multi_pairing(
            vec![
                self.com_avk[0][0],
                self.com_avk[1][0],
                self.com_qx[0][0],
                self.com_qx[1][0],
                self.com_qz[0][0],
                self.com_qz[1][0],
                self.com_bhat[0],
                self.com_q0[0],
                self.com_avk_hat[0][0],
                self.com_avk_hat[1][0],
                self.com_qxhat[0][0],
                self.com_qxhat[1][0],
                self.com_pi[0],
            ],
            vec![
                show_crs.avk[0],
                show_crs.avk[1],
                show_crs.qx[0],
                show_crs.qx[1],
                show_crs.qz[0],
                show_crs.qz[1],
                show_crs.bhat,
                show_crs.q0,
                show_crs.avk_hat[0],
                show_crs.avk_hat[1],
                show_crs.qxhat[0],
                show_crs.qxhat[1],
                show_crs.pi,
            ],
        );
        let rhs = E::pairing(pk.u1[0], self.pi3[0][1])
            + E::pairing(pk.u2[0], self.pi3[1][1])
            + E::pairing(self.theta3[0][0], pk.v1[1])
            + E::pairing(self.theta3[1][0], pk.v2[1]);
        assert_eq!(lhs, rhs);
        // todo: multi_miller

        // check 3
        let lhs = E::pairing(show_crs.b, self.com_b[0])
            + E::pairing(show_crs.com_att, self.com_com_att[0]);
        let rhs = E::pairing(self.theta3[0][1], pk.v1[0])
            + E::pairing(self.theta3[1][1], pk.v2[0])
            + E::pairing(pk.u1[1], self.pi3[0][0])
            + E::pairing(pk.u2[1], self.pi3[1][0]);
        assert_eq!(lhs, rhs);

        // check 4
        let lhs = E::multi_pairing(
            vec![
                show_crs.b,
                show_crs.com_att,
                self.com_avk[0][1],
                self.com_avk[1][1],
                self.com_qx[0][1],
                self.com_qx[1][1],
                self.com_qz[0][1],
                self.com_qz[1][1],
                self.com_bhat[1],
                self.com_q0[1],
                self.com_avk_hat[0][1],
                self.com_avk_hat[1][1],
                self.com_qxhat[0][1],
                self.com_qxhat[1][1],
                self.com_pi[1],
            ],
            vec![
                self.com_b[1],
                self.com_com_att[1],
                show_crs.avk[0],
                show_crs.avk[1],
                show_crs.qx[0],
                show_crs.qx[1],
                show_crs.qz[0],
                show_crs.qz[1],
                show_crs.bhat,
                show_crs.q0,
                show_crs.avk_hat[0],
                show_crs.avk_hat[1],
                show_crs.qxhat[0],
                show_crs.qxhat[1],
                show_crs.pi,
            ],
        );
        let rhs = E::pairing(pk.u1[1], self.pi3[0][1])
            + E::pairing(pk.u2[1], self.pi3[1][1])
            + E::pairing(self.theta3[0][1], pk.v1[1])
            + E::pairing(self.theta3[1][1], pk.v2[1])
            + show_crs.rhs;
        assert_eq!(lhs, rhs);

        // constraint 4
        // check 1
        let lhs = E::pairing(self.com_avk[1][0], self.com_com_att[0]);
        let rhs = E::pairing(self.theta4[0][0], pk.v1[0])
            + E::pairing(self.theta4[1][0], pk.v2[0])
            + E::pairing(pk.u1[0], self.pi4[0][0])
            + E::pairing(pk.u2[0], self.pi4[1][0]);
        assert_eq!(lhs, rhs);

        // check 2
        let lhs = E::pairing(self.com_avk[0][0], E::G2::generator())
            + E::pairing(self.com_avk[1][0], self.com_com_att[1]);
        let rhs = E::pairing(pk.u1[0], self.pi4[0][1])
            + E::pairing(pk.u2[0], self.pi4[1][1])
            + E::pairing(self.theta4[0][0], pk.v1[1])
            + E::pairing(self.theta4[1][0], pk.v2[1]);
        assert_eq!(lhs, rhs);

        // check 3
        let lhs = E::pairing(negg, self.com_s1[0][0])
            + E::pairing(neg_ga, self.com_s1[1][0])
            + E::pairing(crs.ua[0], self.com_s2[0][0])
            + E::pairing(crs.ua[1], self.com_s2[1][0])
            + E::pairing(crs.va[0], self.com_s3[0][0])
            + E::pairing(crs.va[1], self.com_s3[1][0])
            + E::pairing(self.com_avk[1][1], self.com_com_att[0]);
        let rhs = E::pairing(self.theta4[0][1], pk.v1[0])
            + E::pairing(self.theta4[1][1], pk.v2[0])
            + E::pairing(pk.u1[1], self.pi4[0][0])
            + E::pairing(pk.u2[1], self.pi4[1][0]);
        assert_eq!(lhs, rhs);

        // check 4
        let lhs = E::pairing(self.com_avk[0][1], E::G2::generator())
            + E::pairing(self.com_avk[1][1], self.com_com_att[1])
            + E::pairing(negg, self.com_s1[0][1])
            + E::pairing(neg_ga, self.com_s1[1][1])
            + E::pairing(crs.ua[0], self.com_s2[0][1])
            + E::pairing(crs.ua[1], self.com_s2[1][1])
            + E::pairing(crs.va[0], self.com_s3[0][1])
            + E::pairing(crs.va[1], self.com_s3[1][1]);
        let rhs = E::pairing(pk.u1[1], self.pi4[0][1])
            + E::pairing(pk.u2[1], self.pi4[1][1])
            + E::pairing(self.theta4[0][1], pk.v1[1])
            + E::pairing(self.theta4[1][1], pk.v2[1]);
        assert_eq!(lhs, rhs);
    }
}

#[cfg(test)]
mod tests {
    use crate::crs::CRS;
    use crate::gs08;
    use crate::silent_sps::Sig;
    use crate::silent_sps::SK;

    use ark_bls12_381::Bls12_381 as E;
    use ark_bls12_381::Fr as F;
    use ark_bls12_381::G1Projective as G1;
    use ark_bls12_381::G2Projective as G2;
    use ark_ec::pairing::Pairing;
    use ark_ec::PrimeGroup;
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::DenseUVPolynomial;
    use ark_poly::EvaluationDomain;
    use ark_poly::Radix2EvaluationDomain;
    use ark_std::end_timer;
    use ark_std::start_timer;
    use ark_std::{UniformRand, Zero};

    use super::AggregateKey;
    use super::ShowCRS;

    #[test]
    fn test_showing() {
        let n = 1 << 4;
        let t = n / 2;
        let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
        let crs = CRS::<E>::new(n, &mut ark_std::test_rng());
        let mut sk = Vec::new();
        let mut vk = Vec::new();
        let mut hints = Vec::new();
        let mut partial_sigs = Vec::new();

        // sample n random attributes and commit to them
        let att_coeffs = (0..n)
            .map(|_| F::rand(&mut ark_std::test_rng()))
            .collect::<Vec<_>>();

        let att_poly = DensePolynomial::from_coefficients_slice(&att_coeffs);
        let att = att_poly.evaluate_over_domain(domain);

        let com = crs.commit_g2(&att_coeffs);
        let pi = crs.compute_opening_proof(&att_coeffs, &domain.element(1));

        let lhs = E::pairing(G1::generator(), com + (G2::generator() * (-att[1])));
        let rhs = E::pairing(
            pi,
            crs.powers_of_h[1] - (G2::generator() * domain.element(1)),
        );
        assert_eq!(lhs, rhs);

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
                partial_sigs.push(sk[i].sign(&crs, com, &mut ark_std::test_rng()));
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
        let agg_sig = agg_key.agg_sig(&partial_sigs, &selector, crs.clone());

        // verify
        agg_sig.verify(com, t, &agg_key.mvk, &crs);

        let show_crs = ShowCRS::<E>::new(
            &mut ark_std::test_rng(),
            agg_key,
            crs.clone(),
            t,
            domain.element(1),
            att[1],
        );

        let timer = start_timer!(|| "naive");
        let lhs = E::pairing(show_crs.b, agg_sig.b)
            + E::pairing(agg_sig.avk[0], show_crs.avk[0])
            + E::pairing(agg_sig.avk[1], show_crs.avk[1])
            + E::pairing(agg_sig.qx[0], show_crs.qx[0])
            + E::pairing(agg_sig.qx[1], show_crs.qx[1])
            + E::pairing(agg_sig.qz[0], show_crs.qz[0])
            + E::pairing(agg_sig.qz[1], show_crs.qz[1])
            + E::pairing(agg_sig.bhat, show_crs.bhat)
            + E::pairing(agg_sig.q0, show_crs.q0)
            + E::pairing(agg_sig.avk_hat[0], show_crs.avk_hat[0])
            + E::pairing(agg_sig.avk_hat[1], show_crs.avk_hat[1])
            + E::pairing(agg_sig.qxhat[0], show_crs.qxhat[0])
            + E::pairing(agg_sig.qxhat[1], show_crs.qxhat[1])
            + E::pairing(show_crs.com_att, com)
            + E::pairing(pi, show_crs.pi);
        assert_eq!(lhs, show_crs.rhs);
        end_timer!(timer);

        let timer = start_timer!(|| "optimized");
        let lhs_args = vec![
            show_crs.b,
            agg_sig.avk[0],
            agg_sig.avk[1],
            agg_sig.qx[0],
            agg_sig.qx[1],
            agg_sig.qz[0],
            agg_sig.qz[1],
            agg_sig.bhat,
            agg_sig.q0,
            agg_sig.avk_hat[0],
            agg_sig.avk_hat[1],
            agg_sig.qxhat[0],
            agg_sig.qxhat[1],
            show_crs.com_att,
            pi,
        ];

        let rhs_args = vec![
            agg_sig.b,
            show_crs.avk[0],
            show_crs.avk[1],
            show_crs.qx[0],
            show_crs.qx[1],
            show_crs.qz[0],
            show_crs.qz[1],
            show_crs.bhat,
            show_crs.q0,
            show_crs.avk_hat[0],
            show_crs.avk_hat[1],
            show_crs.qxhat[0],
            show_crs.qxhat[1],
            com,
            show_crs.pi,
        ];

        let lhs = E::multi_pairing(lhs_args, rhs_args);
        end_timer!(timer);

        assert_eq!(lhs, show_crs.rhs);

        let pk = gs08::ProverKey::<E>::setup(&mut ark_std::test_rng());
        let showing = agg_sig.show(com, pi, &show_crs, &crs, &pk, &mut ark_std::test_rng());
        showing.verify(&show_crs, &crs, &pk);
    }
}
