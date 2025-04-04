use ark_ff::FftField;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial,
    Radix2EvaluationDomain,
};
use ark_serialize::CanonicalSerialize;
use std::ops::Mul;

pub fn hash_to_bytes<T: CanonicalSerialize>(inp: T) -> [u8; 32] {
    let mut bytes = Vec::new();
    inp.serialize_uncompressed(&mut bytes).unwrap();
    let hash = blake3::hash(bytes.as_slice());
    let hash_bytes = hash.as_bytes();
    *hash_bytes
}

// 1 at omega^i and 0 elsewhere on domain {omega^i}_{i \in [n]}
pub fn lagrange_poly<F: FftField>(n: usize, i: usize) -> DensePolynomial<F> {
    debug_assert!(i < n);
    //todo: check n is a power of 2
    let mut evals = vec![];
    for j in 0..n {
        let l_of_x: u64 = if i == j { 1 } else { 0 };
        evals.push(F::from(l_of_x));
    }

    //powers of nth root of unity
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    //interpolated polynomial over the n points
    eval_form.interpolate()
}

/// interpolates a polynomial where evaluations on points are zero and the polynomial evaluates to 1 at the point 0
/// panics if points contains 0
pub fn compute_vanishing_poly<F: FftField>(points: &Vec<F>) -> DensePolynomial<F> {
    let mut monomials = Vec::new();
    for i in 0..points.len() {
        monomials.push(DensePolynomial::from_coefficients_vec(vec![
            F::zero() - points[i],
            F::one(),
        ]));
    }

    // assert that points.len() is a power of 2
    assert_eq!(
        points.len().count_ones(),
        1,
        "Implementation demands that n-t is a power of 2. Currently: {}",
        points.len()
    );

    let mut chunk_size = points.len() / 2;
    while chunk_size > 0 {
        for i in 0..chunk_size {
            monomials[i] = &monomials[i] * &monomials[i + chunk_size];
        }
        chunk_size = chunk_size / 2;
    }

    let scale = monomials[0].evaluate(&F::zero());
    let res = monomials[0].clone().mul(scale.inverse().unwrap());

    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as F;

    use ark_std::One;
    use ark_std::Zero;

    #[test]
    fn test_vanishing_poly() {
        let n = 1 << 3;
        let mut points = Vec::new();
        for i in 0..n {
            points.push(F::from(i + 1 as u64));
        }
        let poly = compute_vanishing_poly::<F>(&points);

        for i in 0..n {
            assert_eq!(poly.evaluate(&F::from(i + 1 as u64)), F::zero());
        }

        assert_eq!(poly.evaluate(&F::zero()), F::one());
    }
}
