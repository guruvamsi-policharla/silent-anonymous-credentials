use ark_ec::pairing::Pairing;
use ark_ec::PrimeGroup;
use ark_ec::ScalarMul;
use ark_ec::VariableBaseMSM;
use ark_ff::PrimeField;
use ark_std::One;

#[derive(Clone, Debug)]
pub struct PowersOfTau<E: Pairing> {
    /// Group elements of the form `{ \tau^i G }`, where `i` ranges from 0 to `degree`.
    pub powers_of_g: Vec<E::G1Affine>,
    /// Group elements of the form `{ \tau^i H }`, where `i` ranges from 0 to `degree`.
    pub powers_of_h: Vec<E::G2Affine>,
}

impl<E: Pairing> PowersOfTau<E> {
    pub fn setup(max_degree: usize, tau: E::ScalarField) -> PowersOfTau<E> {
        let g = E::G1::generator();
        let h = E::G2::generator();

        let mut powers_of_tau = vec![E::ScalarField::one()];

        let mut cur = tau;
        for _ in 0..=max_degree {
            powers_of_tau.push(cur);
            cur *= &tau;
        }

        let powers_of_g = g.batch_mul(&powers_of_tau[0..max_degree + 1]);
        let powers_of_h = h.batch_mul(&powers_of_tau[0..max_degree + 1]);

        let pp = PowersOfTau {
            powers_of_g,
            powers_of_h,
        };

        pp
    }

    pub fn commit_g1(params: &PowersOfTau<E>, coeffs: &Vec<E::ScalarField>) -> E::G1 {
        assert!(
            coeffs.len() <= params.powers_of_g.len(),
            "Too many coefficients for the given powers of tau"
        );

        let plain_coeffs = coeffs.iter().map(|c| c.into_bigint()).collect::<Vec<_>>();
        <E::G1 as VariableBaseMSM>::msm_bigint(
            &params.powers_of_g[..coeffs.len()],
            plain_coeffs.as_slice(),
        )
    }

    pub fn commit_g2(params: &PowersOfTau<E>, coeffs: &Vec<E::ScalarField>) -> E::G2 {
        assert!(
            coeffs.len() <= params.powers_of_g.len(),
            "Too many coefficients for the given powers of tau"
        );

        let plain_coeffs = coeffs.iter().map(|c| c.into_bigint()).collect::<Vec<_>>();
        <E::G2 as VariableBaseMSM>::msm_bigint(
            &params.powers_of_h[..coeffs.len()],
            plain_coeffs.as_slice(),
        )
    }
}
