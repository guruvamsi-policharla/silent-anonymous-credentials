use ark_ec::pairing::Pairing;
use ark_std::{rand, UniformRand};

/// Contains implementations for the SXDH based commitment schemes used in Groth-Sahai proofs.
#[derive(Debug, Clone)]
pub struct ProverKey<E: Pairing> {
    pub p1: E::G1,
    pub p2: E::G2,
    pub hg1: E::G1,

    pub u1: [E::G1; 2],
    pub u2: [E::G1; 2],
    pub v1: [E::G2; 2],
    pub v2: [E::G2; 2],

    pub u: [E::G1; 2],
    pub v: [E::G2; 2],

    pub i1: [E::G1; 2],
    pub i2: [E::G2; 2],
}

impl<E: Pairing> ProverKey<E> {
    /// Generates a new commitment key.
    pub fn setup<R: rand::RngCore>(rng: &mut R) -> Self {
        let p1 = E::G1::rand(rng);
        let p2 = E::G2::rand(rng);
        let hg1 = E::G1::rand(rng); //should be output of random oracle -- hashtocurve

        let alpha1 = E::ScalarField::rand(rng);
        let u1 = [p1.clone(), p1 * alpha1];

        let t1 = E::ScalarField::rand(rng);
        let u2 = [u1[0] * t1, u1[1] * t1];

        let alpha2 = E::ScalarField::rand(rng);
        let v1 = [p2.clone(), p2 * alpha2];

        let t2 = E::ScalarField::rand(rng);
        let v2 = [v1[0] * t2, v1[1] * t2];

        let u = [u2[0], u2[1] + p1];
        let v = [v2[0], v2[1] + p2];

        let i1 = [-u[0], -u[1]];
        let i2 = [-v[0], -v[1]];

        ProverKey {
            p1,
            p2,
            hg1,
            u1,
            u2,
            v1,
            v2,
            u,
            v,
            i1,
            i2,
        }
    }

    /// Commit to an Fr element and output a commitment in G1
    pub fn commit_fr1<R: rand::RngCore>(
        &self,
        m: &E::ScalarField,
        rng: &mut R,
    ) -> ([E::G1; 2], E::ScalarField) {
        let r = E::ScalarField::rand(rng);
        (
            [
                (self.u1[0] * r) + (self.u2[0] * m),
                (self.u1[1] * r) + (self.u2[1] * m) + (self.u1[0] * m),
            ],
            r,
        )
    }

    /// Commit to an Fr element and output a commitment in G2
    pub fn commit_fr2<R: rand::RngCore>(
        &self,
        m: &E::ScalarField,
        rng: &mut R,
    ) -> ([E::G2; 2], E::ScalarField) {
        let r = E::ScalarField::rand(rng);
        (
            [
                (self.v1[0] * r) + (self.v2[0] * m),
                (self.v1[1] * r) + (self.v2[1] * m) + (self.v1[0] * m),
            ],
            r,
        )
    }

    /// Commit to a G1 element
    pub fn commit_g1<R: rand::RngCore>(
        &self,
        m: &E::G1,
        rng: &mut R,
    ) -> ([E::G1; 2], [E::ScalarField; 2]) {
        let r = [E::ScalarField::rand(rng), E::ScalarField::rand(rng)];
        (
            [
                (self.u1[0] * r[0]) + (self.u2[0] * r[1]),
                (self.u1[1] * r[0]) + (self.u2[1] * r[1]) + m,
            ],
            r,
        )
    }

    /// Commit to a G2 element
    pub fn commit_g2<R: rand::RngCore>(
        &self,
        m: &E::G2,
        rng: &mut R,
    ) -> ([E::G2; 2], [E::ScalarField; 2]) {
        let r = [E::ScalarField::rand(rng), E::ScalarField::rand(rng)];
        (
            [
                self.v1[0] * r[0] + self.v2[0] * r[1],
                self.v1[1] * r[0] + self.v2[1] * r[1] + m,
            ],
            r,
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ec::{bls12::Bls12, PrimeGroup};
    use ark_std::{test_rng, Zero};

    type Fr = <Bls12<ark_bls12_381::Config> as Pairing>::ScalarField;
    type G1 = <Bls12<ark_bls12_381::Config> as Pairing>::G1;
    type G2 = <Bls12<ark_bls12_381::Config> as Pairing>::G2;
    type E = Bls12_381;

    #[test]
    fn dlog_test() {
        // prove that y = g^x
        let rng = &mut test_rng();
        let pk = ProverKey::<Bls12_381>::setup(rng);

        let x = Fr::rand(rng);
        let y = G1::generator() * x;

        let (com_x, r_x) = pk.commit_fr2(&x, rng);

        // prove
        let theta = G1::generator() * r_x;

        // verify
        // check 1 and check 2 ignored
        // check 3
        let lhs = E::pairing(G1::generator(), com_x[0]);
        let rhs = E::pairing(y, pk.v[0]) + E::pairing(theta, pk.v1[0]);
        assert_eq!(lhs, rhs);

        // check 4
        let lhs = E::pairing(G1::generator(), com_x[1]);
        let rhs = E::pairing(y, pk.v[1]) + E::pairing(theta, pk.v1[1]);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn ppe_test() {
        //prove that e(A,B).e(F,D).e(C,H) = T
        let rng = &mut test_rng();
        let pk = ProverKey::<Bls12_381>::setup(rng);

        let a = G1::rand(rng); //witness
        let b = G2::rand(rng); //witness
        let f = G1::rand(rng); //statement
        let d = G2::rand(rng); //witness
        let c = f; //witness
        let h = d; //statement
        let t = E::pairing(a, b) + E::pairing(f, d) + E::pairing(c, h);

        let (com_a, r_a) = pk.commit_g1(&a, rng);
        let (com_b, r_b) = pk.commit_g2(&b, rng);
        let (com_d, r_d) = pk.commit_g2(&d, rng);
        let (com_c, r_c) = pk.commit_g1(&c, rng);

        // prove
        let mut tt = [[Fr::zero(); 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                tt[i][j] = Fr::rand(rng);
            }
        }

        let mut rs = [[Fr::zero(); 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                rs[i][j] = r_a[i] * r_b[j];
            }
        }

        let mut theta = [[G1::generator(); 2]; 2];
        let mut pi = [[G2::generator(); 2]; 2];

        theta[0][0] = pk.u1[0] * tt[0][0] + pk.u2[0] * tt[1][0];
        theta[1][0] = pk.u1[0] * tt[0][1] + pk.u2[0] * tt[1][1];
        theta[0][1] = pk.u1[1] * tt[0][0] + pk.u2[1] * tt[1][0] + f * r_d[0] + a * r_b[0];
        theta[1][1] = pk.u1[1] * tt[0][1] + pk.u2[1] * tt[1][1] + f * r_d[1] + a * r_b[1];

        pi[0][0] = pk.v1[0] * (rs[0][0] - tt[0][0]) + pk.v2[0] * (rs[0][1] - tt[0][1]);
        pi[1][0] = pk.v1[0] * (rs[1][0] - tt[1][0]) + pk.v2[0] * (rs[1][1] - tt[1][1]);
        pi[0][1] = h * r_c[0]
            + b * r_a[0]
            + pk.v1[1] * (rs[0][0] - tt[0][0])
            + pk.v2[1] * (rs[0][1] - tt[0][1]);
        pi[1][1] = h * r_c[1]
            + b * r_a[1]
            + pk.v1[1] * (rs[1][0] - tt[1][0])
            + pk.v2[1] * (rs[1][1] - tt[1][1]);

        // check 1
        let lhs = E::pairing(com_a[0], com_b[0]);
        let rhs = E::pairing(theta[0][0], pk.v1[0])
            + E::pairing(theta[1][0], pk.v2[0])
            + E::pairing(pk.u1[0], pi[0][0])
            + E::pairing(pk.u2[0], pi[1][0]);
        assert_eq!(lhs, rhs);

        // check 2
        let lhs = E::pairing(com_c[0], h) + E::pairing(com_a[0], com_b[1]);
        let rhs = E::pairing(pk.u1[0], pi[0][1])
            + E::pairing(pk.u2[0], pi[1][1])
            + E::pairing(theta[0][0], pk.v1[1])
            + E::pairing(theta[1][0], pk.v2[1]);
        assert_eq!(lhs, rhs);

        // check 3
        let lhs = E::pairing(f, com_d[0]) + E::pairing(com_a[1], com_b[0]);
        let rhs = E::pairing(theta[0][1], pk.v1[0])
            + E::pairing(theta[1][1], pk.v2[0])
            + E::pairing(pk.u1[1], pi[0][0])
            + E::pairing(pk.u2[1], pi[1][0]);
        assert_eq!(lhs, rhs);

        // check 4
        let lhs =
            E::pairing(f, com_d[1]) + E::pairing(com_c[1], h) + E::pairing(com_a[1], com_b[1]);
        let rhs = E::pairing(pk.u1[1], pi[0][1])
            + E::pairing(pk.u2[1], pi[1][1])
            + E::pairing(theta[0][1], pk.v1[1])
            + E::pairing(theta[1][1], pk.v2[1])
            + t;

        assert_eq!(lhs, rhs);
    }
}
