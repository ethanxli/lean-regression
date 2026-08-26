# Statement audit

## Policy

The audited headline is
`LeanRegression.FixedDesign.gaussMarkov_blue_centered`. Each mathematical hypothesis is classified
as:

- **V — verbatim:** stated directly in a standard textbook formulation.
- **I — implied/equivalent:** mathematically equivalent to, or an explicit basis-free form of, a
  textbook condition.
- **L — Lean encoding artifact:** needed to type or integrate the statement in Lean, rather than a
  substantive statistical assumption.
- **G — genuine generalization:** the formal theorem permits a broader setting than the cited
  finite-dimensional matrix statement.

The comparison sources are Davidson, *An Introduction to Econometric Theory*, Chapter 8,
“The Gauss–Markov Theorem,” pp. 109–119
([DOI](https://doi.org/10.1002/9781119484905.ch8)), and Davidson–MacKinnon,
*Econometric Theory and Methods*, §3.5, pp. 104–107
([author-hosted book page](https://qed.econ.queensu.ca/ETM/etm-info.html)). The latter writes a
competing estimator as `Ay`, imposes unbiasedness, and proves that its covariance exceeds the OLS
covariance by a positive-semidefinite term.

## Headline theorem, hypothesis by hypothesis

| Lean hypothesis or binder | Textbook counterpart | Class | Audit note |
|---|---|---:|---|
| `P` is a real inner-product space and `FiniteDimensional ℝ P` | Coefficient vector `β ∈ ℝᵏ` | I | A choice of coordinates identifies finite-dimensional `P` with Euclidean coefficient space. |
| `CompleteSpace P` and additive/normed typeclasses | Completeness of `ℝᵏ` | L | Split into instances so Mathlib can supply adjoints, integrals, and inverses. In finite dimensions completeness follows mathematically. |
| `O` is a complete real inner-product space | Observation vector `y ∈ ℝⁿ` | G | Textbooks use finite `n`; the proof only needs a Hilbert observation space and a finite-dimensional design range. |
| `D : FixedDesign P O` with `D.map : P →L[ℝ] O` | Fixed, nonstochastic design matrix `X` | I | A continuous linear map is the coordinate-free matrix. “Fixed design” is represented by making `D` data, not a random variable. |
| `D.injective` | `X` has full column rank | V | This is exactly the no-perfect-multicollinearity/full-rank condition. It makes `X†X` invertible. |
| `μ : Measure O` and `IsProbabilityMeasure μ` | Error vector has a probability law | I | The textbook random vector `ε` is represented by its law. No sample-space choice is needed. |
| `hμ : MemLp id 2 μ` | Errors have finite second moments | V | Required for expectations, variances, covariance pushforwards, and the response-law bridge. |
| `hcentered : ∫ ε, ε ∂μ = 0` | `E[ε] = 0` | V | Deliberately separate from covariance. Omitting this would still prove covariance optimality, but would not justify the word “unbiased” in its expectation sense. |
| `hcov : IsIsotropicCovariance μ σ2` | `Cov(ε) = σ² I`, equivalently equal variances and zero cross-covariances | I | Defined as `covarianceBilin μ u v = σ² ⟪u,v⟫` for all directions. In an orthonormal coordinate basis this is exactly the usual matrix condition. It does **not** encode centering. |
| `hσ2 : 0 ≤ σ2` | A variance is nonnegative | V | Follows from `hcov` when `O` is nontrivial. It is explicit so the theorem also handles the degenerate zero observation space without adding a `Nontrivial O` instance. |
| `MeasurableSpace O`, `BorelSpace O` | Euclidean random vectors are Borel measurable | L | Bookkeeping needed to define vector integrals and covariance in Mathlib. |
| `MeasurableSpace P`, `BorelSpace P`, `SecondCountableTopology P` | Linear estimators of a Euclidean random vector are measurable | L | These instances let Mathlib form the estimator pushforward law. They add no statistical restriction in finite-dimensional Euclidean coordinates. |
| `A : O →L[ℝ] P` | A competing estimator `Ay`, linear in observations | I | In textbook finite dimensions every linear map is continuous. Continuity matters only because `O` is generalized to a Hilbert space. |
| `hA : D.IsLinearUnbiasedEstimator A`, definitionally `A ∘L D.map = id` | `AX = I`, hence `Eβ[Ay] = β` for every `β` | I | This is global, not pointwise: the condition and the theorem's expectation conclusions quantify over **all** parameter values. Centering is used to connect the left-inverse equation to expectations. |

## Conclusion audit

The first two conjuncts state, for every `β : P`,

```text
Eμ[OLS(Xβ + ε)] = β     and     Eμ[A(Xβ + ε)] = β.
```

The third states, again for every `β`, that

```text
Covβ(Ay) - Covβ(OLS y)
```

is positive semidefinite. This is the Loewner-order reading of “best.” Evaluating the bilinear
form on any `u : P` gives the equivalent scalar statement that every linear contrast `⟪u, β⟫`
has no smaller variance under `A` than under OLS. The library proves the stronger exact gap
identity before deriving positivity.

No Gaussian assumption appears. No independence assumption appears. “Uncorrelated with equal
variance” is covariance information and is strictly weaker than independence.

## Deliberate nearby distinctions

- `gaussMarkov_blue` is the algebraic covariance theorem. It needs neither centering nor finite
  moments beyond those implicit in the covariance form, and it calls candidates “unbiased” only
  in the design-left-inverse sense.
- `gaussMarkov_blue_responseLaw` moves the covariance comparison to actual estimator laws but
  still does not claim expectation-unbiasedness.
- `gaussMarkov_blue_centered` is the public audited headline because it includes the missing
  expectation bridge explicitly.
- `aitken_gls_blue` assumes an **operational whitening equivalence**. In finite-dimensional
  Euclidean space this is the standard positive-definite covariance model. For infinite-dimensional
  `O`, a bounded invertible whitening map is stronger than mere injective positivity; the source
  docstring and [scope document](SCOPE.md) say so.

## FWL source alignment

The FWL reference statement is Davidson, *An Introduction to Econometric Theory*, §11.2,
pp. 155–156 ([DOI](https://doi.org/10.1002/9781119484905.ch11)); a second standard source is Hill,
Griffiths, and Lim, *Principles of Econometrics*, 5th ed., §5.2.4
([publisher table of contents](https://www.stata.com/bookstore/principles-of-econometrics/)).
The formal scalar theorem uses an abstract nuisance subspace; the vector theorem uses a finite
regressor family; and the fixed-design endpoint states that the coefficient block from joint OLS
equals the coefficient from residualized regression. These are basis-free forms of the textbook
partitioned-matrix statement, not weaker normal-equation-only surrogates.
