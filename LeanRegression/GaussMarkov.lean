import LeanRegression.Covariance

set_option linter.style.header false

/-!
# Gauss–Markov theorem

The main result is an exact variance-gap identity.  For every unbiased scalar contrast weight, its
variance is the OLS variance plus the nonnegative squared norm of its component orthogonal to the
design range.  Applying the scalar identity to every parameter-space direction yields the vector
BLUE statement as positivity of the covariance-form difference.
-/

namespace LeanRegression

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {P O : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [FiniteDimensional ℝ P]
  [NormedAddCommGroup O] [InnerProductSpace ℝ O] [CompleteSpace O]

namespace FixedDesign

variable (D : FixedDesign P O)

theorem contrastWeight_difference_mem_orthogonal {c : P} {a : O}
    (ha : D.IsUnbiasedContrast c a) :
    a - D.olsContrastWeight c ∈ D.map.rangeᗮ := by
  rw [ContinuousLinearMap.orthogonal_range]
  change D.map.adjoint (a - D.olsContrastWeight c) = 0
  rw [map_sub, ha, D.olsContrastWeight_unbiased c, sub_self]

theorem contrastWeight_orthogonal {c : P} {a : O}
    (ha : D.IsUnbiasedContrast c a) :
    inner ℝ (D.olsContrastWeight c) (a - D.olsContrastWeight c) = 0 := by
  exact D.contrastWeight_difference_mem_orthogonal ha
    (D.olsContrastWeight c) (D.olsContrastWeight_mem_range c)

/-- Deterministic minimum-norm identity behind Gauss–Markov. -/
theorem contrastWeight_norm_sq_decomposition {c : P} {a : O}
    (ha : D.IsUnbiasedContrast c a) :
    ‖a‖ ^ 2 = ‖D.olsContrastWeight c‖ ^ 2 +
      ‖a - D.olsContrastWeight c‖ ^ 2 := by
  have hsplit : a = D.olsContrastWeight c + (a - D.olsContrastWeight c) := by
    abel
  calc
    ‖a‖ ^ 2 = ‖D.olsContrastWeight c + (a - D.olsContrastWeight c)‖ ^ 2 := by
      exact congrArg (fun z : O ↦ ‖z‖ ^ 2) hsplit
    _ = ‖D.olsContrastWeight c‖ ^ 2 + ‖a - D.olsContrastWeight c‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
          (D.contrastWeight_orthogonal ha)

/-- Exact covariance-form gap for every unbiased scalar contrast under spherical errors. -/
theorem gaussMarkov_contrast_covariance_gap
    [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} {σ2 : ℝ} (hcov : IsIsotropicCovariance μ σ2)
    {c : P} {a : O} (ha : D.IsUnbiasedContrast c a) :
    covarianceBilin μ a a =
      covarianceBilin μ (D.olsContrastWeight c) (D.olsContrastWeight c) +
        σ2 * ‖a - D.olsContrastWeight c‖ ^ 2 := by
  rw [hcov.apply, hcov.apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, D.contrastWeight_norm_sq_decomposition ha]
  ring

/-- **Scalar Gauss–Markov variance-gap identity.** No Gaussianity or independence is required. -/
theorem gaussMarkov_contrast_variance_gap
    [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} [IsFiniteMeasure μ] (hμ : MemLp id 2 μ)
    {σ2 : ℝ} (hcov : IsIsotropicCovariance μ σ2)
    {c : P} {a : O} (ha : D.IsUnbiasedContrast c a) :
    Var[fun z ↦ inner ℝ a z; μ] =
      Var[fun z ↦ inner ℝ (D.olsContrastWeight c) z; μ] +
        σ2 * ‖a - D.olsContrastWeight c‖ ^ 2 := by
  rw [← covarianceBilin_self hμ, ← covarianceBilin_self hμ]
  exact D.gaussMarkov_contrast_covariance_gap hcov ha

/-- Exact vector covariance gap, evaluated on an arbitrary parameter contrast. -/
theorem gaussMarkov_estimatorCovariance_gap
    [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} {σ2 : ℝ} (hcov : IsIsotropicCovariance μ σ2)
    (A : O →L[ℝ] P) (hA : D.IsLinearUnbiasedEstimator A) (u : P) :
    estimatorCovariance μ A u u =
      estimatorCovariance μ D.ols u u +
        σ2 * ‖(A - D.ols).adjoint u‖ ^ 2 := by
  have hcontrast : D.IsUnbiasedContrast u (A.adjoint u) :=
    D.unbiased_adjoint_weight A hA u
  have hgap := D.gaussMarkov_contrast_covariance_gap hcov hcontrast
  have hadjoint : (A - D.ols).adjoint u = A.adjoint u - D.ols.adjoint u := by
    rw [map_sub]
    rfl
  rw [hadjoint]
  exact hgap

/-- **Vector Gauss–Markov theorem (BLUE).** The covariance of any linear unbiased estimator minus
the OLS covariance is positive semidefinite in Loewner order. -/
theorem gaussMarkov_blue
    [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (hcov : IsIsotropicCovariance μ σ2)
    (A : O →L[ℝ] P) (hA : D.IsLinearUnbiasedEstimator A) :
    (estimatorCovariance μ A - estimatorCovariance μ D.ols).toBilinForm.IsPosSemidef := by
  refine ⟨estimatorCovariance_sub_isSymm μ A D.ols, ⟨fun u ↦ ?_⟩⟩
  simp only [ContinuousLinearMap.toBilinForm_apply, sub_apply]
  have hgap := D.gaussMarkov_estimatorCovariance_gap hcov A hA u
  rw [hgap]
  simpa only [add_sub_cancel_left] using
    mul_nonneg hσ2 (sq_nonneg ‖(A - D.ols).adjoint u‖)

/-- On a nontrivial observation space, covariance nonnegativity supplies the nonnegative isotropic
scale required by the vector BLUE theorem. -/
theorem gaussMarkov_blue_of_nontrivial
    [MeasurableSpace O] [BorelSpace O] [Nontrivial O]
    {μ : Measure O} {σ2 : ℝ} (hcov : IsIsotropicCovariance μ σ2)
    (A : O →L[ℝ] P) (hA : D.IsLinearUnbiasedEstimator A) :
    (estimatorCovariance μ A - estimatorCovariance μ D.ols).toBilinForm.IsPosSemidef :=
  D.gaussMarkov_blue hcov.nonneg hcov A hA

/-- **Law-level vector Gauss–Markov theorem.** Under a square-integrable error law, the covariance
form of the estimator's actual pushforward response law dominates that of OLS.  This is the vector
counterpart of a `Var` statement: vector variance is represented by its covariance bilinear form. -/
theorem gaussMarkov_blue_responseLaw
    [MeasurableSpace O] [BorelSpace O]
    [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    {μ : Measure O} [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    {σ2 : ℝ} (hσ2 : 0 ≤ σ2) (hcov : IsIsotropicCovariance μ σ2)
    (β : P) (A : O →L[ℝ] P) (hA : D.IsLinearUnbiasedEstimator A) :
    (covarianceBilin ((D.responseLaw μ β).map A) -
      covarianceBilin ((D.responseLaw μ β).map D.ols)).toBilinForm.IsPosSemidef := by
  rw [covarianceBilin_estimator_responseLaw (D := D) hμ β A,
    covarianceBilin_estimator_responseLaw (D := D) hμ β D.ols]
  exact D.gaussMarkov_blue hσ2 hcov A hA

/-- **Audited Gauss–Markov theorem (BLUE).** Centering is stated separately from isotropic
covariance so the usual expectation-based meaning of unbiasedness is explicit.  The first two
conjuncts say, for every parameter value, that OLS and the competing linear estimator have the
correct expectation.  The last conjunct is the Loewner-order covariance comparison under the
actual response law. -/
theorem gaussMarkov_blue_centered
    [MeasurableSpace O] [BorelSpace O]
    [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    {μ : Measure O} [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hcentered : ∫ ε, ε ∂μ = 0)
    {σ2 : ℝ} (hσ2 : 0 ≤ σ2) (hcov : IsIsotropicCovariance μ σ2)
    (A : O →L[ℝ] P) (hA : D.IsLinearUnbiasedEstimator A) :
    (∀ β : P, ∫ ε, D.ols (D.response β ε) ∂μ = β) ∧
      (∀ β : P, ∫ ε, A (D.response β ε) ∂μ = β) ∧
        ∀ β : P,
          (covarianceBilin ((D.responseLaw μ β).map A) -
            covarianceBilin ((D.responseLaw μ β).map D.ols)).toBilinForm.IsPosSemidef := by
  have hintegrable : Integrable (id : O → O) μ := hμ.integrable (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro β
    exact D.integral_estimate_response D.ols D.ols_isLinearUnbiasedEstimator β id
      hintegrable hcentered
  · intro β
    exact D.integral_estimate_response A hA β id hintegrable hcentered
  · intro β
    exact D.gaussMarkov_blue_responseLaw hμ hσ2 hcov β A hA

/-- OLS is the unique linear unbiased estimator attaining the same covariance form in every
parameter direction when the spherical variance is strictly positive. -/
theorem gaussMarkov_blue_unique
    [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} {σ2 : ℝ} (hσ2 : 0 < σ2)
    (hcov : IsIsotropicCovariance μ σ2)
    (A : O →L[ℝ] P) (hA : D.IsLinearUnbiasedEstimator A)
    (heq : estimatorCovariance μ A = estimatorCovariance μ D.ols) :
    A = D.ols := by
  have hzero (u : P) : ‖(A - D.ols).adjoint u‖ ^ 2 = 0 := by
    have hgap := D.gaussMarkov_estimatorCovariance_gap hcov A hA u
    rw [heq] at hgap
    have hproduct : σ2 * ‖(A - D.ols).adjoint u‖ ^ 2 = 0 := by
      linarith
    exact (mul_eq_zero.mp hproduct).resolve_left hσ2.ne'
  have hadjoint : (A - D.ols).adjoint = 0 := by
    ext u
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hzero u))
  have hdifference : A - D.ols = 0 := by
    have h := congrArg ContinuousLinearMap.adjoint hadjoint
    simpa [FixedDesign.ols] using h
  exact sub_eq_zero.mp hdifference

/-- OLS is the unique BLUE when the spherical error variance is strictly positive. -/
theorem gaussMarkov_contrast_unique
    [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} {σ2 : ℝ} (hσ2 : 0 < σ2)
    (hcov : IsIsotropicCovariance μ σ2)
    {c : P} {a : O} (ha : D.IsUnbiasedContrast c a)
    (heq : covarianceBilin μ a a =
      covarianceBilin μ (D.olsContrastWeight c) (D.olsContrastWeight c)) :
    a = D.olsContrastWeight c := by
  have hgap := D.gaussMarkov_contrast_covariance_gap hcov ha
  rw [heq] at hgap
  have hzero : ‖a - D.olsContrastWeight c‖ ^ 2 = 0 := by
    have hproduct : σ2 * ‖a - D.olsContrastWeight c‖ ^ 2 = 0 := by
      linarith
    exact (mul_eq_zero.mp hproduct).resolve_left hσ2.ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

end FixedDesign

end

end LeanRegression
