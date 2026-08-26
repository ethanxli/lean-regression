# Scope and limitations

## What is proved

- Coordinate-free OLS for a full-column-rank fixed design.
- Exact loss decompositions, minimality, and uniqueness of OLS.
- Scalar FWL, finite-family vector FWL, and the concrete partitioned-design block coefficient
  identity.
- Scalar contrast and vector covariance Gauss–Markov gap identities.
- BLUE as a positive-semidefinite covariance-form difference (Loewner order).
- Expectation-unbiasedness for every parameter under a centered error law.
- GLS/Aitken after transport through a bounded invertible whitening transformation.
- Conditional expectation as the unique minimum-MSE predictor in `L²`.

## What is not claimed

- No random-design, conditional-on-design, or endogeneity theorem is yet formalized.
- No asymptotic consistency, asymptotic normality, standard-error, confidence-interval, or
  hypothesis-test result is claimed.
- No claim is made that uncorrelated errors are independent.
- No Gaussian distribution is assumed or derived.
- The Aitken interface does not derive a whitening equivalence from an arbitrary abstract positive
  covariance operator in infinite dimensions. The equivalence is supplied as data.
- FWL currently treats real Hilbert geometry and finite regressor blocks; rank-deficient designs
  via Moore–Penrose inverses are out of scope.
- “Best” always means covariance domination among **linear** estimators unbiased for every
  parameter, not minimum risk among all nonlinear estimators.

## Representation choices

Textbook matrices are continuous linear maps. Transpose is the Hilbert adjoint. Covariance matrices
are continuous bilinear forms. Matrix positive-semidefiniteness is positivity of the associated
bilinear form. These choices avoid committing the core proofs to a basis while recovering the
standard finite-dimensional formulas after choosing coordinates.
