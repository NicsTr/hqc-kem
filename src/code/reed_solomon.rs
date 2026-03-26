use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Sub};

use hybrid_array::typenum::Unsigned;
use hybrid_array::{
    Array, ArraySize,
    sizes::{U1, U2, U16, U24, U32, U46, U56, U90},
    typenum::{Diff, NonZero, Quot, Sum},
};

use ctutils::{Choice, CtAssign, CtEq, CtGt, CtOption, CtSelect};

use crate::code::gf256::Gf256;
use crate::{Hqc1, Hqc3, Hqc5};

impl ShortenedByteReedSolomonParam for Hqc1 {
    type ExternalMessageBytesize = U16;
    type ExternalCodewordBytesize = U46;
    const GEN_POLY: Array<u8, Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>> =
        Array([
            89, 69, 153, 116, 176, 117, 111, 75, 73, 233, 242, 233, 65, 210, 21, 139, 103, 173, 67,
            118, 105, 210, 174, 110, 74, 69, 228, 82, 255, 181,
        ]);
}

impl ShortenedByteReedSolomonParam for Hqc3 {
    type ExternalMessageBytesize = U24;
    type ExternalCodewordBytesize = U56;
    const GEN_POLY: Array<u8, Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>> =
        Array([
            45, 216, 239, 24, 253, 104, 27, 40, 107, 50, 163, 210, 227, 134, 224, 158, 119, 13,
            158, 1, 238, 164, 82, 43, 15, 232, 246, 142, 50, 189, 29, 232,
        ]);
}

impl ShortenedByteReedSolomonParam for Hqc5 {
    type ExternalMessageBytesize = U32;
    type ExternalCodewordBytesize = U90;
    const GEN_POLY: Array<u8, Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>> =
        Array([
            49, 167, 49, 39, 200, 121, 124, 91, 240, 63, 148, 71, 150, 123, 87, 101, 32, 215, 159,
            71, 201, 115, 97, 210, 186, 183, 141, 217, 123, 12, 31, 243, 180, 219, 152, 239, 99,
            141, 4, 246, 191, 144, 8, 232, 47, 27, 141, 178, 130, 64, 124, 47, 39, 188, 216, 48,
            199, 187,
        ]);
}

// Parameters and implementation have different visibilities
pub trait ShortenedByteReedSolomonParam: Clone
where
    Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>:
        ArraySize + NonZero + Div<U2>,
    Quot<Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>, U2>:
        ArraySize + Add<U1>,
    Sum<Quot<Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>, U2>, U1>:
        ArraySize + NonZero,
{
    type ExternalMessageBytesize: ArraySize;
    type ExternalCodewordBytesize: ArraySize + NonZero + Sub<Self::ExternalMessageBytesize>;
    const GEN_POLY: Array<u8, Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>>;
}

/// An `ExternalCode` is something that encodes a `MessageBytesize` bytes message into
/// an array of `CodewordBytesize` bytes. Those elements are meant
/// to be later encoded by an `InternalCode`.
pub(crate) trait ExternalCode: ShortenedByteReedSolomon {
    /// From Lin, Costello, 1983, Section 4.3
    fn encode_external(
        message: &Array<u8, Self::ExternalMessageBytesize>,
    ) -> Array<u8, Self::ExternalCodewordBytesize> {
        let mut c = Array::<Gf256, Self::ExternalCodewordBytesize>::default();

        let parity_check_size = Self::ParityCheckBytesize::USIZE;
        let dimension = Self::ExternalMessageBytesize::USIZE;

        for i in 0..dimension {
            let gate = Gf256(message[dimension - 1 - i]) + c[parity_check_size - 1];

            let tmp: Array<Gf256, Self::ParityCheckBytesize> =
                Array::from_fn(|i| gate * Gf256(Self::GEN_POLY[i]));

            // Add gated value and clock one time
            for k in (1..parity_check_size).rev() {
                c[k] = c[k - 1] + tmp[k];
            }

            c[0] = tmp[0];
        }

        Array::from_fn(|i| {
            if i < parity_check_size {
                c[i].0
            } else {
                message[i - parity_check_size]
            }
        })
    }

    // FIXME:
    /// From Lin, Costello, 1983, Section FIXME
    fn decode_external(
        codeword: &Array<u8, Self::ExternalCodewordBytesize>,
    ) -> Array<u8, Self::ExternalMessageBytesize> {
        let syndromes = Self::compute_syndromes(codeword);

        let (error_locator_polynomial, n_errors) = Self::compute_elp(&syndromes);
        let error_positions = Self::compute_error_positions(&error_locator_polynomial);
        let z = Self::compute_z(error_locator_polynomial, syndromes, n_errors);
        let error_values = Self::compute_error_values(error_positions, z);

        Array::from_fn(|i| {
            error_values
                [Diff::<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>::USIZE + i]
                .0
                ^ codeword
                    [Diff::<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>::USIZE
                        + i]
        })
    }
}

impl<RS: ShortenedByteReedSolomonParam> ExternalCode for RS {}

pub(crate) trait CtEqZero {
    fn ct_eq_zero(&self) -> Choice;

    fn ct_nz(&self) -> Choice {
        !self.ct_eq_zero()
    }
}

impl CtEqZero for u8 {
    fn ct_eq_zero(&self) -> Choice {
        self.ct_eq(&0u8)
    }

    fn ct_nz(&self) -> Choice {
        self.ct_ne(&0u8)
    }
}

pub(crate) trait ShortenedByteReedSolomon: ShortenedByteReedSolomonParam {
    type ParityCheckBytesize: ArraySize;

    /// Compute syndromes by evaluating codeword at multiples evaluation points
    /// (successive powers of 2 in the field)
    fn compute_syndromes(
        codeword: &Array<u8, Self::ExternalCodewordBytesize>,
    ) -> Array<Gf256, Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>> {
        // Ensure this property at compile time.
        const {
            assert!(
                Diff::<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>::USIZE + 1
                    < 256
            )
        };

        // TODO: Optimize here, by computing evaluation points only once
        // or by precomputing them.
        Array::from_fn(|i| {
            let alpha = Gf256(2).pow((i + 1) as u8);
            let mut v = alpha;

            let mut res = Gf256(codeword[0]);
            for j in 1..Self::ExternalCodewordBytesize::USIZE {
                res += v * Gf256(codeword[j]);
                v *= alpha;
            }

            res
        })
    }

    /// Compute error-locator polynomial by using Berlekamp algorithm as described in
    /// Lin and Costello, 1983, Section 6.2. Return the error-locator polynomial and
    /// the number of errors found.
    ///
    /// Be careful to do it in constant time.
    fn compute_elp(
        syndromes: &Array<
            Gf256,
            Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>,
        >,
    ) -> (
        RsPolynomial<
            Sum<Quot<Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>, U2>, U1>,
        >,
        u8,
    ) {
        // Start with initial values for mu = 0
        let mut x_sigma_p = RsPolynomial::x();
        let mut d_p = Gf256(1);
        let mut degree_x_sigma_p = 1u8;

        let mut sigma_mu = RsPolynomial::one();
        let mut d_mu = syndromes[0];
        let mut degree_sigma_mu = 0;

        let parity_check_size =
            Diff::<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>::USIZE;
        let max_correctable_error =
            Quot::<Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>, U2>::USIZE;

        // Iterate the berlekamp algorithm
        for mu in 0..parity_check_size {
            let current_sigma_mu = sigma_mu.clone();
            let current_degree_sigma_mu = degree_sigma_mu;

            // Update sigma with curr_sigma_p.
            // If d(sigma) == 0, this update will leave sigma unchanged, as intended,
            // thanks to the multiplication by d(sigma).
            sigma_mu += (d_mu * d_p.inv()) * &x_sigma_p;

            // End loop condition here, to avoid out of bound
            if mu + 1 == parity_check_size {
                break;
            }

            // Condition is:
            //  d(current_sigma_mu) != 0 and mu - degree(current_sigma_mu) > p - degree(sigma_p)
            //  <=> d(current_sigma_mu) != 0 and (p + degree_x) - degree(current_sigma_mu) > p - degree(sigma_p)
            //  <=> d(current_sigma_mu) != 0 and degree_x + degree(sigma_p) > degree(current_sigma_mu)
            let cond_update = d_mu.ct_nz() & degree_x_sigma_p.ct_gt(&current_degree_sigma_mu);

            // Update discrepency of sigma_p
            d_p.ct_assign(&d_mu, cond_update);

            // Update degree of sigma_mu
            degree_sigma_mu.ct_assign(&degree_x_sigma_p, cond_update);

            // Update x_sigma_p
            //
            // Perform conditional assignment and multiply by X at the same time
            //
            // - x_sigma_p[0] = 0 is invariant
            // - degree_x_sigma_p starts at 1. When update condition is true,
            // it takes a strictly lesser value, then is incremented. Else, it is incremented.
            // Thus, its maximum value is mu + 1, and no overflow can happen during
            // multiplication by X.
            for i in (1..=max_correctable_error).rev() {
                x_sigma_p.coeffs[i] = Gf256::ct_select(
                    &x_sigma_p.coeffs[i - 1],
                    &current_sigma_mu.coeffs[i - 1],
                    cond_update,
                );
            }

            // Update degree of x_sigma_p
            degree_x_sigma_p.ct_assign(&current_degree_sigma_mu, cond_update);
            degree_x_sigma_p += 1;

            // Update current discrepency for next round
            d_mu = syndromes[mu + 1];
            // TODO: Can be further restricted (and thus optimised),
            // since the degree of sigma_mu is the number of errors found,
            // which is in turn bound by the maximum distance.
            for i in 1..=(mu + 1).min(max_correctable_error) {
                // FIXME: re-evaluate: Guaranteed to be always in bound since (mu + 1) always stays in bound
                d_mu += sigma_mu.coeffs[i] * syndromes[mu + 1 - i];
            }
        }

        (sigma_mu, degree_sigma_mu)
    }

    /// Return the array representing the error positions by evaluating `poly`
    /// at the first `Self::N` evaluation point inverse.
    ///
    /// The returned array contains a CtOption that is None everywhere except
    /// at indexes `i`s where `2**(-i)` is a root `poly`. In the latter case, the
    /// element is a CtOption that is `Some(2**i)`.
    ///
    // TODO: this could be optimized by using another root finding algorithm.
    // Maybe Horner's method, Chien search, or FFT-based method
    // (like in the HQC reference implementation).
    fn compute_error_positions(
        elp_poly: &RsPolynomial<
            Sum<Quot<Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>, U2>, U1>,
        >,
    ) -> Array<CtOption<Gf256>, Self::ExternalCodewordBytesize> {
        let mut beta = Gf256(1);
        let mut beta_inv = Gf256(1);
        let inv_two = Gf256(2).inv(); // TODO: make it const

        Array::from_fn(|_| {
            // Evaluate `poly` at evaluation point
            let value = elp_poly.evaluate(&beta_inv);
            let beta_cpy = beta;

            // Update evaluation point
            beta *= Gf256(2);
            beta_inv *= inv_two;

            CtOption::new(beta_cpy, value.ct_eq(&Gf256(0)))
        })
    }

    /// Compute the "Z" polynomial from the error-locator polynomial and the syndromes.
    fn compute_z(
        elp_poly: RsPolynomial<
            Sum<Quot<Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>, U2>, U1>,
        >,
        syndromes: Array<
            Gf256,
            Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>,
        >,
        n_errors: u8,
    ) -> RsPolynomial<
        Sum<Quot<Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>, U2>, U1>,
    > {
        let mut z = elp_poly.clone();

        let max_correctable_error =
            Quot::<Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>, U2>::USIZE;
        for i in 1..=max_correctable_error {
            z.coeffs[i] += syndromes[i - 1].ct_select(&Gf256(0), i.ct_gt(&(n_errors as usize)));

            for j in 1..i {
                z.coeffs[i] += (elp_poly.coeffs[j] * syndromes[i - j - 1])
                    .ct_select(&Gf256(0), i.ct_gt(&(n_errors as usize)));
            }
        }
        z
    }

    /// Compute the error values given their positions and the "Z" polynomial.
    /// Return the error array.
    ///
    // TODO: compute only on the relevant values (the last N - K)
    fn compute_error_values(
        mut error_positions: Array<CtOption<Gf256>, Self::ExternalCodewordBytesize>,
        z: RsPolynomial<
            Sum<Quot<Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>, U2>, U1>,
        >,
    ) -> Array<Gf256, Self::ExternalCodewordBytesize> {
        let mut beta_inv = Gf256(1);
        let inv_two = Gf256(2).inv(); // TODO: make it const

        Array::from_fn(|i| {
            // When not at an error position, the result of all computations
            // will be (safely) discarded at the end
            let numerator = z.evaluate(&beta_inv);

            let mut inv_denominator = Gf256(1);
            for (j, beta) in error_positions.iter_mut().enumerate() {
                inv_denominator *= Gf256(1)
                    // Exclude values that are not error positions and the current position
                    + beta
                        .unwrap_or(Gf256(0))
                        .ct_select(&Gf256(0), j.ct_eq(&i))
                        * beta_inv;
            }

            // Update beta_inv
            beta_inv *= inv_two;

            (numerator * inv_denominator.inv()).ct_select(&Gf256(0), error_positions[i].is_none())
        })
    }
}

impl<RS: ShortenedByteReedSolomonParam> ShortenedByteReedSolomon for RS {
    type ParityCheckBytesize = Diff<Self::ExternalCodewordBytesize, Self::ExternalMessageBytesize>;
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct RsPolynomial<N: ArraySize + NonZero> {
    coeffs: Array<Gf256, N>,
}

impl<N: ArraySize + NonZero> From<Array<u8, N>> for RsPolynomial<N> {
    fn from(value: Array<u8, N>) -> Self {
        RsPolynomial {
            coeffs: Array::from_fn(|i| value[i].into()),
        }
    }
}

impl<N: ArraySize + NonZero> From<RsPolynomial<N>> for Array<u8, N> {
    fn from(value: RsPolynomial<N>) -> Self {
        Array::from_fn(|i| value.coeffs[i].0)
    }
}

impl<N: ArraySize + NonZero> RsPolynomial<N> {
    fn x() -> Self {
        // Ensure polynomial is big enough at compile time.
        const { assert!(N::USIZE > 1) };
        let mut coeffs = Array::default();
        coeffs[1] = Gf256(1);

        RsPolynomial { coeffs }
    }

    fn evaluate(&self, point: &Gf256) -> Gf256 {
        let mut v = *point;

        let mut res = self.coeffs[0];
        for j in 1..N::USIZE {
            res += v * self.coeffs[j];
            v *= *point;
        }

        res
    }

    fn one() -> Self {
        let mut coeffs = Array::default();
        // Cannot fail since N is non-zero.
        coeffs[0] = Gf256(1);
        RsPolynomial { coeffs }
    }
}

impl<N: ArraySize + NonZero> Add for RsPolynomial<N> {
    type Output = RsPolynomial<N>;

    fn add(self, rhs: Self) -> Self::Output {
        RsPolynomial {
            // Does not panic since the Map iterator has exactly the right number of element
            // (same as Zip iterator, which is in turn the same as self and rhs)
            coeffs: Array::from_iter(self.coeffs.iter().zip(rhs.coeffs).map(|(l, r)| *l + r)),
        }
    }
}

impl<N: ArraySize + NonZero> AddAssign for RsPolynomial<N> {
    fn add_assign(&mut self, rhs: Self) {
        for (ai, bj) in self.coeffs.iter_mut().zip(rhs.coeffs) {
            *ai += bj;
        }
    }
}

impl<N: ArraySize + NonZero> Mul<&RsPolynomial<N>> for Gf256 {
    type Output = RsPolynomial<N>;

    fn mul(self, rhs: &RsPolynomial<N>) -> Self::Output {
        RsPolynomial {
            coeffs: Array::from_fn(|i| self * rhs.coeffs[i]),
        }
    }
}

impl<N: ArraySize + NonZero> MulAssign<Gf256> for RsPolynomial<N> {
    fn mul_assign(&mut self, rhs: Gf256) {
        for c in self.coeffs.iter_mut() {
            *c *= rhs;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::hash::XofState;
    use hybrid_array::sizes::U2;
    use rand::RngExt;
    use rand::distr::{Distribution, StandardUniform};
    use rand::{Rng, SeedableRng, rngs::StdRng};

    impl<N: ArraySize + NonZero> Distribution<RsPolynomial<N>> for StandardUniform {
        fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> RsPolynomial<N> {
            Array::from_fn(|_| rng.random()).into()
        }
    }

    fn test_zero_syndrome<RS: ShortenedByteReedSolomonParam>(
        codeword: Array<u8, RS::ExternalCodewordBytesize>,
    ) {
        assert_eq!(RS::compute_syndromes(&codeword), Array::default());
    }

    fn test_nonzero_syndrome<RS: ShortenedByteReedSolomonParam>(
        codeword: Array<u8, RS::ExternalCodewordBytesize>,
    ) {
        assert_ne!(RS::compute_syndromes(&codeword), Array::default());
    }

    fn gen_noise<RS: ShortenedByteReedSolomonParam>(
        rng: &mut StdRng,
    ) -> Array<u8, RS::ExternalCodewordBytesize> {
        let seed: [u8; 8] = rng.random();
        let mut xof = XofState::new(&seed);
        let support: Array<usize, _> =
            xof.generate_random_support_biased::<Quot<Diff<RS::ExternalCodewordBytesize, RS::ExternalMessageBytesize>, U2>, RS::ExternalCodewordBytesize>();

        let mut res = Array::default();
        for v in support {
            res[v] = rng.random(); // Can be zero, but it's okay here.
        }
        res.into()
    }

    fn test_encoding_and_syndromes<RS: ShortenedByteReedSolomonParam>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..100 {
            let message = Array::from_fn(|_| rng.random());

            test_zero_syndrome::<RS>(RS::encode_external(&message));
        }

        for _ in 0..100 {
            let message = Array::from_fn(|_| rng.random());

            let codeword = RS::encode_external(&message);

            let noisy_codeword = RsPolynomial::<RS::ExternalCodewordBytesize>::from(codeword)
                + gen_noise::<RS>(&mut rng).into();

            test_nonzero_syndrome::<RS>(noisy_codeword.into());
        }
    }

    #[test]
    fn test_encode_hqc1rs() {
        let message = Array([
            202, 48, 44, 62, 103, 240, 103, 102, 145, 190, 93, 206, 31, 140, 78, 229,
        ]);

        let codeword = Hqc1::encode_external(&message);
        let expected = Array([
            239, 195, 82, 1, 191, 86, 194, 73, 235, 59, 99, 202, 210, 230, 140, 79, 62, 75, 6, 172,
            69, 61, 63, 183, 36, 148, 132, 253, 192, 225, 202, 48, 44, 62, 103, 240, 103, 102, 145,
            190, 93, 206, 31, 140, 78, 229,
        ]);

        assert_eq!(codeword, expected);
    }

    #[test]
    fn test_encode_hqc3rs() {
        let message = Array([
            198, 223, 10, 99, 149, 248, 255, 192, 149, 203, 211, 187, 15, 245, 106, 82, 183, 76,
            52, 201, 195, 54, 40, 167,
        ]);

        let codeword = Hqc3::encode_external(&message);
        let expected = Array([
            44, 201, 215, 222, 4, 2, 190, 88, 93, 152, 240, 155, 168, 68, 8, 215, 144, 93, 24, 251,
            90, 214, 184, 242, 160, 152, 248, 59, 193, 106, 117, 53, 198, 223, 10, 99, 149, 248,
            255, 192, 149, 203, 211, 187, 15, 245, 106, 82, 183, 76, 52, 201, 195, 54, 40, 167,
        ]);

        assert_eq!(codeword, expected);
    }

    #[test]
    fn test_encode_hqc5rs() {
        let message = Array([
            210, 4, 199, 20, 34, 187, 70, 5, 64, 163, 117, 134, 69, 121, 215, 46, 115, 15, 30, 127,
            164, 107, 51, 154, 159, 40, 179, 60, 118, 179, 23, 58,
        ]);

        let codeword = Hqc5::encode_external(&message);
        let expected = Array([
            48, 33, 138, 215, 50, 132, 243, 36, 37, 159, 94, 128, 12, 120, 255, 158, 130, 216, 173,
            229, 204, 104, 43, 49, 58, 174, 255, 29, 146, 108, 221, 76, 213, 58, 79, 170, 248, 189,
            28, 212, 69, 200, 173, 76, 100, 254, 47, 226, 182, 181, 198, 52, 93, 172, 27, 204, 208,
            69, 210, 4, 199, 20, 34, 187, 70, 5, 64, 163, 117, 134, 69, 121, 215, 46, 115, 15, 30,
            127, 164, 107, 51, 154, 159, 40, 179, 60, 118, 179, 23, 58,
        ]);

        assert_eq!(codeword, expected);
    }

    #[test]
    fn test_zero_syndrome_hqc1rs() {
        let codeword = Array([
            121, 33, 0, 164, 7, 86, 128, 132, 17, 2, 71, 13, 166, 217, 17, 234, 254, 117, 235, 75,
            91, 227, 140, 239, 128, 59, 20, 84, 179, 59, 210, 4, 199, 20, 34, 187, 70, 5, 64, 163,
            117, 134, 69, 121, 215, 46,
        ]);
        test_zero_syndrome::<Hqc1>(codeword);
    }

    #[test]
    fn test_zero_syndrome_hqc3rs() {
        let codeword = Array([
            44, 201, 215, 222, 4, 2, 190, 88, 93, 152, 240, 155, 168, 68, 8, 215, 144, 93, 24, 251,
            90, 214, 184, 242, 160, 152, 248, 59, 193, 106, 117, 53, 198, 223, 10, 99, 149, 248,
            255, 192, 149, 203, 211, 187, 15, 245, 106, 82, 183, 76, 52, 201, 195, 54, 40, 167,
        ]);
        test_zero_syndrome::<Hqc3>(codeword);
    }

    #[test]
    fn test_zero_syndrome_hqc5rs() {
        let codeword = Array([
            48, 33, 138, 215, 50, 132, 243, 36, 37, 159, 94, 128, 12, 120, 255, 158, 130, 216, 173,
            229, 204, 104, 43, 49, 58, 174, 255, 29, 146, 108, 221, 76, 213, 58, 79, 170, 248, 189,
            28, 212, 69, 200, 173, 76, 100, 254, 47, 226, 182, 181, 198, 52, 93, 172, 27, 204, 208,
            69, 210, 4, 199, 20, 34, 187, 70, 5, 64, 163, 117, 134, 69, 121, 215, 46, 115, 15, 30,
            127, 164, 107, 51, 154, 159, 40, 179, 60, 118, 179, 23, 58,
        ]);
        test_zero_syndrome::<Hqc5>(codeword);
    }

    #[test]
    fn test_encoding_and_syndromes_hqc1rs() {
        test_encoding_and_syndromes::<Hqc1>(1337);
    }

    #[test]
    fn test_encoding_and_syndromes_hqc3rs() {
        test_encoding_and_syndromes::<Hqc3>(1338);
    }

    #[test]
    fn test_encoding_and_syndromes_hqc5rs() {
        test_encoding_and_syndromes::<Hqc5>(1339);
    }

    fn test_elp<RS: ShortenedByteReedSolomonParam>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..100 {
            let noise = gen_noise::<RS>(&mut rng);

            let syndromes = RS::compute_syndromes(&noise);

            let (error_locator_polynomial, _) = RS::compute_elp(&syndromes);

            // Check that, at an error position, the inverse evaluation point
            // is indeed a root of the error-locating polynomial.
            // And also check that the converse is also true.
            //
            // Check that
            for i in 0..RS::ExternalCodewordBytesize::USIZE {
                assert!(i < 256);
                let pos = Gf256(2).pow(i as u8);

                if noise[i] != 0 {
                    assert_eq!(error_locator_polynomial.evaluate(&pos.inv()), Gf256(0));
                } else {
                    assert_ne!(error_locator_polynomial.evaluate(&pos.inv()), Gf256(0));
                }
            }
        }
    }

    #[test]
    fn test_elp_hqc1rs() {
        test_elp::<Hqc1>(1337);
    }

    #[test]
    fn test_elp_hqc3rs() {
        test_elp::<Hqc3>(1338);
    }

    #[test]
    fn test_elp_hqc5rs() {
        test_elp::<Hqc5>(1339);
    }

    fn test_error_positions<RS: ShortenedByteReedSolomonParam>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..100 {
            let noise = gen_noise::<RS>(&mut rng);

            let syndromes = RS::compute_syndromes(&noise);

            let (error_locator_polynomial, _) = RS::compute_elp(&syndromes);
            let error_positions = RS::compute_error_positions(&error_locator_polynomial);

            for (i, v) in error_positions.iter().enumerate() {
                assert!(i < 256);
                let beta = Gf256(2).pow(i as u8);

                if v.into_option().is_none() {
                    assert_eq!(noise[i], 0);
                } else {
                    assert_ne!(noise[i], 0);
                    assert_eq!(*v.as_inner_unchecked(), beta);
                }
            }
        }
    }

    #[test]
    fn test_error_positions_hqc1rs() {
        test_error_positions::<Hqc1>(1337);
    }

    #[test]
    fn test_error_positions_hqc3rs() {
        test_error_positions::<Hqc3>(1338);
    }

    #[test]
    fn test_error_positions_hqc5rs() {
        test_error_positions::<Hqc5>(1339);
    }

    fn test_error_values<RS: ShortenedByteReedSolomonParam>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..100 {
            let noise = gen_noise::<RS>(&mut rng);

            let syndromes = RS::compute_syndromes(&noise);

            let (error_locator_polynomial, n_errors) = RS::compute_elp(&syndromes);
            let error_positions = RS::compute_error_positions(&error_locator_polynomial);

            let z = RS::compute_z(error_locator_polynomial, syndromes, n_errors);

            let error_values = RS::compute_error_values(error_positions, z);

            for (v1, v2) in error_values.into_iter().zip(noise) {
                assert_eq!(v1, Gf256(v2));
            }
        }
    }

    #[test]
    fn test_error_values_hqc1rs() {
        test_error_values::<Hqc1>(1340);
    }

    #[test]
    fn test_error_values_hqc3rs() {
        test_error_values::<Hqc3>(1341);
    }

    #[test]
    fn test_error_values_hqc5rs() {
        test_error_values::<Hqc5>(1342);
    }

    fn test_perfect<RS: ShortenedByteReedSolomonParam>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..100 {
            let message = Array::<u8, RS::ExternalMessageBytesize>::from_fn(|_| rng.random());

            assert_eq!(
                message,
                RS::decode_external(&RS::encode_external(&(message)))
            );
        }
    }

    #[test]
    fn test_perfect_hqc1rs() {
        test_perfect::<Hqc1>(1312);
    }

    #[test]
    fn test_perfect_hqc3rs() {
        test_perfect::<Hqc3>(1341);
    }

    #[test]
    fn test_perfect_hqc5rs() {
        test_perfect::<Hqc5>(1342);
    }

    fn test_noisy<RS: ShortenedByteReedSolomonParam>(seed: u64) {
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..100 {
            let message = Array::<u8, RS::ExternalMessageBytesize>::from_fn(|_| rng.random());
            let noise = gen_noise::<RS>(&mut rng);

            let codeword = &RS::encode_external(&(message));
            let noisy_codeword = Array::from_fn(|i| codeword[i] ^ noise[i]);

            assert_eq!(message, RS::decode_external(&noisy_codeword));
        }
    }

    #[test]
    fn test_noisy_hqc1rs() {
        test_noisy::<Hqc1>(1313);
    }

    #[test]
    fn test_noisy_hqc3rs() {
        test_noisy::<Hqc3>(1342);
    }

    #[test]
    fn test_noisy_hqc5rs() {
        test_noisy::<Hqc5>(1343);
    }
}
