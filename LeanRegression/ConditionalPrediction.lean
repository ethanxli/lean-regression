import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option linter.style.header false

/-!
# Conditional expectation as the optimal mean-square predictor

This module gives a regression-facing API for the Hilbert-space interpretation of conditional
expectation. A square-integrable random variable is represented by `Lp ℝ 2 P`; its conditional
expectation is the orthogonal projection onto the closed subspace of random variables measurable
with respect to the information sigma-algebra.

The main result is the exact risk decomposition

`E[(Y - g)²] = E[(Y - E[Y | m])²] + E[(E[Y | m] - g)²]`

for every square-integrable, `m`-measurable predictor `g`. Minimality and uniqueness follow.
-/

open MeasureTheory
open scoped ENNReal

namespace LeanRegression

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {P : Measure[m₀] Ω}

/-- Mean-squared prediction error for two square-integrable real random variables.

The `Lp` norm is the root-mean-square norm, so its square is the usual expected squared error.
See `meanSquaredError_eq_integral` for the integral form. -/
noncomputable def meanSquaredError (target predictor : Ω →₂[P] ℝ) : ℝ :=
  ‖target - predictor‖ ^ 2

theorem meanSquaredError_nonneg (target predictor : Ω →₂[P] ℝ) :
    0 ≤ meanSquaredError target predictor :=
  sq_nonneg _

@[simp]
theorem meanSquaredError_self (target : Ω →₂[P] ℝ) :
    meanSquaredError target target = 0 := by
  simp [meanSquaredError]

/-- The Hilbert-space definition of mean-squared error is the expected squared pointwise error. -/
theorem meanSquaredError_eq_integral (target predictor : Ω →₂[P] ℝ) :
    meanSquaredError target predictor = ∫ ω, (target ω - predictor ω) ^ 2 ∂P := by
  rw [meanSquaredError, ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub target predictor] with ω hω
  rw [Real.inner_apply]
  rw [pow_two, hω]
  rfl

/-- The conditional mean as an `L²` predictor. It is mathlib's `condExpL2`, coerced from the
subspace of `m`-measurable `L²` functions back to the ambient `L²` space. -/
noncomputable def conditionalPredictor (hm : m ≤ m₀) (target : Ω →₂[P] ℝ) : Ω →₂[P] ℝ :=
  (condExpL2 ℝ ℝ hm target : Ω →₂[P] ℝ)

theorem conditionalPredictor_aestronglyMeasurable (hm : m ≤ m₀) (target : Ω →₂[P] ℝ) :
    AEStronglyMeasurable[m] (conditionalPredictor hm target : Ω → ℝ) P := by
  exact aestronglyMeasurable_condExpL2 hm target

/-- The residual after conditional-mean prediction is orthogonal to every square-integrable
predictor measurable with respect to the available information. -/
theorem residual_inner_eq_zero (hm : m ≤ m₀) (target predictor : Ω →₂[P] ℝ)
    (hpredictor : AEStronglyMeasurable[m] predictor P) :
    inner ℝ (target - conditionalPredictor hm target) predictor = 0 := by
  rw [inner_sub_left, conditionalPredictor,
    inner_condExpL2_eq_inner_fun hm target predictor hpredictor, sub_self]

/-- Pythagorean decomposition of prediction risk. This is the population analogue of the usual
regression decomposition into irreducible error and approximation error. -/
theorem meanSquaredError_decomposition (hm : m ≤ m₀) (target predictor : Ω →₂[P] ℝ)
    (hpredictor : AEStronglyMeasurable[m] predictor P) :
    meanSquaredError target predictor =
      meanSquaredError target (conditionalPredictor hm target) +
        meanSquaredError (conditionalPredictor hm target) predictor := by
  have hmeasurableDiff :
      AEStronglyMeasurable[m] (conditionalPredictor hm target - predictor) P :=
    ((conditionalPredictor_aestronglyMeasurable hm target).sub hpredictor).congr
      (Lp.coeFn_sub (conditionalPredictor hm target) predictor).symm
  have horthogonal :
      inner ℝ (target - conditionalPredictor hm target)
        (conditionalPredictor hm target - predictor) = 0 :=
    residual_inner_eq_zero hm target _ hmeasurableDiff
  unfold meanSquaredError
  rw [show target - predictor =
      (target - conditionalPredictor hm target) +
        (conditionalPredictor hm target - predictor) by abel]
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthogonal

/-- Conditional expectation minimizes mean-squared prediction error among all square-integrable
predictors measurable with respect to the information sigma-algebra. -/
theorem conditionalPredictor_minimal (hm : m ≤ m₀) (target predictor : Ω →₂[P] ℝ)
    (hpredictor : AEStronglyMeasurable[m] predictor P) :
    meanSquaredError target (conditionalPredictor hm target) ≤
      meanSquaredError target predictor := by
  rw [meanSquaredError_decomposition hm target predictor hpredictor]
  exact le_add_of_nonneg_right (meanSquaredError_nonneg _ _)

/-- The conditional-mean predictor is the unique `m`-measurable `L²` predictor attaining its
minimum mean-squared error. -/
theorem conditionalPredictor_unique (hm : m ≤ m₀) (target predictor : Ω →₂[P] ℝ)
    (hpredictor : AEStronglyMeasurable[m] predictor P)
    (hoptimal : meanSquaredError target predictor =
      meanSquaredError target (conditionalPredictor hm target)) :
    predictor = conditionalPredictor hm target := by
  have hdecomposition := meanSquaredError_decomposition hm target predictor hpredictor
  rw [hoptimal] at hdecomposition
  have hrisk : meanSquaredError (conditionalPredictor hm target) predictor = 0 := by
    linarith
  have hnorm : ‖conditionalPredictor hm target - predictor‖ = 0 := by
    rw [meanSquaredError] at hrisk
    exact sq_eq_zero_iff.mp hrisk
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

/-- On a finite measure space, the `L²` conditional predictor agrees almost everywhere with the
usual function-valued conditional expectation. -/
theorem conditionalPredictor_ae_eq_condExp [IsFiniteMeasure P] (hm : m ≤ m₀)
    {target : Ω → ℝ} (htarget : MemLp target 2 P) :
    (conditionalPredictor hm (htarget.toLp target) : Ω → ℝ) =ᵐ[P]
      condExp m P target := by
  exact htarget.condExpL2_ae_eq_condExp hm

end LeanRegression

