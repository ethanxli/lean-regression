import LeanRegression.LinearEstimator
import Mathlib.Probability.Moments.CovarianceBilin

set_option linter.style.header false

/-!
# Covariance of linear estimators

Covariances are represented by Mathlib's coordinate-free continuous bilinear forms.  Pulling such
a form back along the adjoint of an estimator is the operator-free form of the usual sandwich
covariance formula.
-/

namespace LeanRegression

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {P O : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup O] [InnerProductSpace ℝ O] [CompleteSpace O]

/-- Pull a covariance form on the observation space back through a linear estimator. -/
def pullbackCovariance (covForm : O →L[ℝ] O →L[ℝ] ℝ) (A : O →L[ℝ] P) :
    P →L[ℝ] P →L[ℝ] ℝ :=
  covForm.bilinearComp A.adjoint A.adjoint

@[simp]
theorem pullbackCovariance_apply (covForm : O →L[ℝ] O →L[ℝ] ℝ) (A : O →L[ℝ] P)
    (u v : P) :
    pullbackCovariance covForm A u v = covForm (A.adjoint u) (A.adjoint v) :=
  rfl

/-- Covariance of the estimation error induced by an observation-space error law. -/
def estimatorCovariance [MeasurableSpace O] [BorelSpace O]
    (μ : Measure O) (A : O →L[ℝ] P) : P →L[ℝ] P →L[ℝ] ℝ :=
  pullbackCovariance (covarianceBilin μ) A

@[simp]
theorem estimatorCovariance_apply [MeasurableSpace O] [BorelSpace O]
    (μ : Measure O) (A : O →L[ℝ] P) (u v : P) :
    estimatorCovariance μ A u v =
      covarianceBilin μ (A.adjoint u) (A.adjoint v) :=
  rfl

theorem estimatorCovariance_comm [MeasurableSpace O] [BorelSpace O]
    (μ : Measure O) (A : O →L[ℝ] P) (u v : P) :
    estimatorCovariance μ A u v = estimatorCovariance μ A v u := by
  simp only [estimatorCovariance_apply, covarianceBilin_comm]

/-- A difference of estimator covariance forms is symmetric. -/
theorem estimatorCovariance_sub_isSymm [MeasurableSpace O] [BorelSpace O]
    (μ : Measure O) (A B : O →L[ℝ] P) :
    (estimatorCovariance μ A - estimatorCovariance μ B).toBilinForm.IsSymm := by
  refine ⟨fun u v ↦ ?_⟩
  simp only [ContinuousLinearMap.toBilinForm_apply, sub_apply]
  rw [estimatorCovariance_comm μ A, estimatorCovariance_comm μ B]

/-- The pullback definition agrees with the covariance of the pushforward estimator law. -/
theorem estimatorCovariance_eq_covarianceBilin_map
    [MeasurableSpace O] [BorelSpace O]
    [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    {μ : Measure O} [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) (A : O →L[ℝ] P) :
    estimatorCovariance μ A = covarianceBilin (μ.map A) := by
  ext u v
  rw [estimatorCovariance_apply, covarianceBilin_map hμ]

/-- A spherical covariance assumption, stated without choosing coordinates. -/
def IsIsotropicCovariance [MeasurableSpace O] [BorelSpace O]
    (μ : Measure O) (σ2 : ℝ) : Prop :=
  covarianceBilin μ = σ2 • innerSL ℝ

omit [CompleteSpace O] in
theorem IsIsotropicCovariance.apply [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} {σ2 : ℝ} (h : IsIsotropicCovariance μ σ2) (x y : O) :
    covarianceBilin μ x y = σ2 * inner ℝ x y := by
  rw [h]
  rfl

omit [CompleteSpace O] in
/-- On a nontrivial observation space, the scale in an isotropic covariance identity is
automatically nonnegative.  Keeping the scale hypothesis explicit in degenerate-space theorems
avoids imposing `Nontrivial O` throughout the API. -/
theorem IsIsotropicCovariance.nonneg [MeasurableSpace O] [BorelSpace O] [Nontrivial O]
    {μ : Measure O} {σ2 : ℝ} (h : IsIsotropicCovariance μ σ2) : 0 ≤ σ2 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : O)
  have hdiag : 0 ≤ covarianceBilin μ x x := covarianceBilin_self_nonneg x
  rw [h.apply, real_inner_self_eq_norm_sq] at hdiag
  exact nonneg_of_mul_nonneg_left hdiag (sq_pos_of_pos (norm_pos_iff.mpr hx))

namespace FixedDesign

variable [FiniteDimensional ℝ P]
variable (D : FixedDesign P O)

/-- The fixed-design response distribution induced by an error law. -/
def responseLaw [MeasurableSpace O] (μ : Measure O) (β : P) : Measure O :=
  μ.map (fun ε ↦ D.map β + ε)

omit [CompleteSpace P] [FiniteDimensional ℝ P] in
/-- Translating an error law by the fitted mean does not change its covariance. -/
theorem covarianceBilin_responseLaw [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} [IsProbabilityMeasure μ] (β : P) :
    covarianceBilin (D.responseLaw μ β) = covarianceBilin μ := by
  exact covarianceBilin_map_const_add (μ := μ) (D.map β)

omit [CompleteSpace P] [FiniteDimensional ℝ P] [CompleteSpace O] in
/-- Translating a square-integrable error law by the fitted mean remains square-integrable. -/
theorem responseLaw_memLp [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) (β : P) :
    MemLp id 2 (D.responseLaw μ β) := by
  exact (measurableEmbedding_addLeft (D.map β)).memLp_map_measure_iff.mpr
    ((memLp_const (D.map β)).add hμ)

omit [FiniteDimensional ℝ P] in
/-- Estimator covariance is unchanged when the observation law is translated by its fixed-design
mean. -/
theorem estimatorCovariance_responseLaw [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} [IsProbabilityMeasure μ] (β : P) (A : O →L[ℝ] P) :
    estimatorCovariance (D.responseLaw μ β) A = estimatorCovariance μ A := by
  unfold estimatorCovariance
  rw [D.covarianceBilin_responseLaw]

omit [FiniteDimensional ℝ P] in
/-- The covariance of an estimator under the actual response law is the pullback covariance used
throughout the fixed-design API.  This composes the response-law and pushforward-law bridges. -/
theorem covarianceBilin_estimator_responseLaw
    [MeasurableSpace O] [BorelSpace O]
    [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    {μ : Measure O} [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (β : P) (A : O →L[ℝ] P) :
    covarianceBilin ((D.responseLaw μ β).map A) = estimatorCovariance μ A := by
  let : IsProbabilityMeasure (D.responseLaw μ β) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  rw [← estimatorCovariance_eq_covarianceBilin_map (D.responseLaw_memLp hμ β) A,
    estimatorCovariance_responseLaw (D := D)]

/-- The explicit coordinate-free OLS sandwich `H X† Σ X H`, represented as a bilinear form. -/
def olsSandwichCovariance (covForm : O →L[ℝ] O →L[ℝ] ℝ) :
    P →L[ℝ] P →L[ℝ] ℝ :=
  covForm.bilinearComp (D.map ∘L D.gramInverse) (D.map ∘L D.gramInverse)

@[simp]
theorem olsSandwichCovariance_apply (covForm : O →L[ℝ] O →L[ℝ] ℝ) (u v : P) :
    D.olsSandwichCovariance covForm u v =
      covForm (D.map (D.gramInverse u)) (D.map (D.gramInverse v)) :=
  rfl

/-- **Exact OLS sandwich covariance identity**, valid for an arbitrary error covariance. -/
theorem ols_estimatorCovariance_eq_sandwich [MeasurableSpace O] [BorelSpace O]
    (μ : Measure O) :
    estimatorCovariance μ D.ols = D.olsSandwichCovariance (covarianceBilin μ) := by
  ext u v
  simp [estimatorCovariance_apply, D.ols_adjoint]

/-- Under spherical errors, the OLS covariance is `σ² (X†X)⁻¹`. -/
theorem ols_estimatorCovariance_isotropic [MeasurableSpace O] [BorelSpace O]
    {μ : Measure O} {σ2 : ℝ} (hcov : IsIsotropicCovariance μ σ2) (u v : P) :
    estimatorCovariance μ D.ols u v = σ2 * inner ℝ (D.gramInverse u) v := by
  rw [estimatorCovariance_apply, D.ols_adjoint, hcov.apply]
  congr 1
  change inner ℝ (D.map (D.gramInverse u)) (D.map (D.gramInverse v)) = _
  rw [← D.map.adjoint_inner_right]
  change inner ℝ (D.gramInverse u) (D.gram (D.gramInverse v)) = _
  rw [D.gram_apply_gramInverse]

end FixedDesign

end

end LeanRegression
