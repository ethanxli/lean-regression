import LeanRegression.Design
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false

/-!
# Frisch–Waugh–Lovell theorem

This module develops FWL as one connected API:

* the scalar theorem for an abstract nuisance subspace;
* the finite-family vector theorem, including normal equations, rank, loss, and uniqueness;
* the concrete fixed-design interface, including the residual-maker identity and the theorem that
  the regressor block of joint OLS equals the residualized-regression coefficient.

Residualization is a continuous linear map, finite fitted values use
`Fintype.linearCombination`, and the fixed-design results derive the required projection and
residualized full-rank facts from the design hypotheses.
-/

namespace LeanRegression

noncomputable section

section Scalar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Remove the orthogonal projection onto the nuisance subspace `U`.

Bundling residualization as a continuous linear map exposes its linearity directly and lets the
abstract FWL development interoperate with concrete least-squares operators. -/
noncomputable def residualize (U : Submodule ℝ E) [U.HasOrthogonalProjection] : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - U.starProjection

theorem residualize_apply (U : Submodule ℝ E) [U.HasOrthogonalProjection] (z : E) :
    residualize U z = z - U.starProjection z :=
  rfl

/-- The one-regressor least-squares coefficient. The nonzero-regressor hypothesis is imposed on
theorems using this definition rather than on the definition itself. -/
noncomputable def simpleRegressionCoefficient (regressor outcome : E) : ℝ :=
  inner ℝ regressor outcome / inner ℝ regressor regressor

/-- The FWL coefficient: regress the residualized outcome on the residualized regressor. -/
noncomputable def partialRegressionCoefficient (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressor outcome : E) : ℝ :=
  simpleRegressionCoefficient (residualize U regressor) (residualize U outcome)

/-- For a fixed coefficient `β`, this is the least-squares nuisance fit. -/
noncomputable def profiledNuisanceFit (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressor outcome : E) (β : ℝ) : E :=
  U.starProjection (outcome - β • regressor)

/-- The residual from the joint fit after optimizing the nuisance component at coefficient `β`. -/
noncomputable def profiledResidual (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressor outcome : E) (β : ℝ) : E :=
  outcome - (profiledNuisanceFit U regressor outcome β + β • regressor)

/-- The joint squared-error objective after profiling out the nuisance coefficients. -/
noncomputable def profiledSquaredError (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressor outcome : E) (β : ℝ) : ℝ :=
  ‖profiledResidual U regressor outcome β‖ ^ 2

section Projection

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

theorem residualize_mem_orthogonal (z : E) : residualize U z ∈ Uᗮ := by
  exact Submodule.sub_starProjection_mem_orthogonal z

/-- Residualization vanishes exactly when the vector is already in the nuisance subspace. Thus the
FWL nondegeneracy assumption says precisely that the regressor of interest is not collinear with
the nuisance regressors. -/
@[simp]
theorem residualize_eq_zero_iff (z : E) : residualize U z = 0 ↔ z ∈ U := by
  constructor
  · intro hzero
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hzero).symm
  · intro hz
    exact sub_eq_zero.mpr (Submodule.starProjection_eq_self_iff.mpr hz).symm

theorem residualize_ne_zero_iff (z : E) : residualize U z ≠ 0 ↔ z ∉ U := by
  exact not_congr (residualize_eq_zero_iff U z)

theorem residualize_sub_smul (outcome regressor : E) (β : ℝ) :
    residualize U (outcome - β • regressor) =
      residualize U outcome - β • residualize U regressor := by
  rw [map_sub, map_smul]

theorem profiledNuisanceFit_mem (regressor outcome : E) (β : ℝ) :
    profiledNuisanceFit U regressor outcome β ∈ U := by
  exact Submodule.starProjection_apply_mem U _

/-- Profiling the nuisance coefficient is exactly residualization by `U`. -/
theorem profiledResidual_eq_residualize (regressor outcome : E) (β : ℝ) :
    profiledResidual U regressor outcome β = residualize U (outcome - β • regressor) := by
  simp only [profiledResidual, profiledNuisanceFit, residualize_apply]
  abel

/-- The algebraic heart of FWL: the profiled joint residual is the residualized-regression
residual. -/
theorem profiledResidual_eq_residualized (regressor outcome : E) (β : ℝ) :
    profiledResidual U regressor outcome β =
      residualize U outcome - β • residualize U regressor := by
  rw [profiledResidual_eq_residualize, residualize_sub_smul]

theorem profiledResidual_mem_orthogonal (regressor outcome : E) (β : ℝ) :
    profiledResidual U regressor outcome β ∈ Uᗮ := by
  rw [profiledResidual_eq_residualize]
  exact residualize_mem_orthogonal U _

/-- Exact Pythagorean decomposition showing that `profiledNuisanceFit` really is the least-squares
nuisance fit for a fixed coefficient. -/
theorem nuisanceFit_squaredError_decomposition (regressor outcome : E) (β : ℝ)
    {nuisanceFit : E} (hnuisanceFit : nuisanceFit ∈ U) :
    ‖outcome - (nuisanceFit + β • regressor)‖ ^ 2 =
      profiledSquaredError U regressor outcome β +
        ‖profiledNuisanceFit U regressor outcome β - nuisanceFit‖ ^ 2 := by
  have hprofiledOrthogonal := profiledResidual_mem_orthogonal U regressor outcome β
  have hnuisanceDifference :
      profiledNuisanceFit U regressor outcome β - nuisanceFit ∈ U :=
    U.sub_mem (profiledNuisanceFit_mem U regressor outcome β) hnuisanceFit
  have horthogonal :
      inner ℝ (profiledResidual U regressor outcome β)
        (profiledNuisanceFit U regressor outcome β - nuisanceFit) = 0 := by
    rw [real_inner_comm]
    exact hprofiledOrthogonal _ hnuisanceDifference
  have hsplit :
      outcome - (nuisanceFit + β • regressor) =
        profiledResidual U regressor outcome β +
          (profiledNuisanceFit U regressor outcome β - nuisanceFit) := by
    unfold profiledResidual
    abel
  rw [hsplit, profiledSquaredError]
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthogonal

/-- Profiling the nuisance component minimizes squared error among all nuisance fits in `U`. -/
theorem profiledNuisanceFit_minimal (regressor outcome : E) (β : ℝ)
    {nuisanceFit : E} (hnuisanceFit : nuisanceFit ∈ U) :
    profiledSquaredError U regressor outcome β ≤
      ‖outcome - (nuisanceFit + β • regressor)‖ ^ 2 := by
  rw [nuisanceFit_squaredError_decomposition U regressor outcome β hnuisanceFit]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- In the profiled normal equation, the original regressor can be replaced by its residualized
version because the profiled residual is orthogonal to the nuisance subspace. -/
theorem inner_regressor_profiledResidual_eq_inner_residualized
    (regressor outcome : E) (β : ℝ) :
    inner ℝ regressor (profiledResidual U regressor outcome β) =
      inner ℝ (residualize U regressor) (profiledResidual U regressor outcome β) := by
  have horthogonal := profiledResidual_mem_orthogonal U regressor outcome β
  have hprojection :
      inner ℝ (U.starProjection regressor) (profiledResidual U regressor outcome β) = 0 :=
    horthogonal _ (Submodule.starProjection_apply_mem U regressor)
  rw [← sub_eq_zero, ← inner_sub_left]
  have hdifference : regressor - residualize U regressor = U.starProjection regressor := by
    simp [residualize]
  rw [hdifference]
  exact hprojection

end Projection

section SimpleRegression

/-- The residual at the simple-regression coefficient is orthogonal to the regressor. -/
theorem simpleRegression_residual_inner_eq_zero {regressor outcome : E}
    (hregressor : regressor ≠ 0) :
    inner ℝ regressor
      (outcome - simpleRegressionCoefficient regressor outcome • regressor) = 0 := by
  have hinner : inner ℝ regressor regressor ≠ 0 := inner_self_ne_zero.mpr hregressor
  rw [inner_sub_right, real_inner_smul_right, simpleRegressionCoefficient]
  rw [div_mul_cancel₀ _ hinner]
  exact sub_self _

/-- For a nonzero regressor, the scalar normal equation has exactly the ordinary least-squares
coefficient as its solution. -/
theorem simpleRegression_normalEquation_iff {regressor outcome : E}
    (hregressor : regressor ≠ 0) (β : ℝ) :
    inner ℝ regressor (outcome - β • regressor) = 0 ↔
      β = simpleRegressionCoefficient regressor outcome := by
  have hinner : inner ℝ regressor regressor ≠ 0 := inner_self_ne_zero.mpr hregressor
  constructor
  · intro hnormal
    rw [inner_sub_right, real_inner_smul_right] at hnormal
    rw [simpleRegressionCoefficient, eq_div_iff hinner]
    exact (sub_eq_zero.mp hnormal).symm
  · rintro rfl
    exact simpleRegression_residual_inner_eq_zero hregressor

/-- Exact one-regressor least-squares loss decomposition. -/
theorem simpleRegression_squaredError_decomposition {regressor outcome : E}
    (hregressor : regressor ≠ 0) (β : ℝ) :
    ‖outcome - β • regressor‖ ^ 2 =
      ‖outcome - simpleRegressionCoefficient regressor outcome • regressor‖ ^ 2 +
        (β - simpleRegressionCoefficient regressor outcome) ^ 2 * ‖regressor‖ ^ 2 := by
  let βhat := simpleRegressionCoefficient regressor outcome
  have hnormal : inner ℝ regressor (outcome - βhat • regressor) = 0 := by
    exact simpleRegression_residual_inner_eq_zero hregressor
  have horthogonal :
      inner ℝ (outcome - βhat • regressor) ((βhat - β) • regressor) = 0 := by
    rw [real_inner_smul_right, real_inner_comm, hnormal, mul_zero]
  have hsplit :
      outcome - β • regressor =
        (outcome - βhat • regressor) + (βhat - β) • regressor := by
    module
  rw [hsplit]
  calc
    ‖outcome - βhat • regressor + (βhat - β) • regressor‖ ^ 2 =
        ‖outcome - βhat • regressor‖ ^ 2 + ‖(βhat - β) • regressor‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthogonal
    _ = ‖outcome - βhat • regressor‖ ^ 2 + (β - βhat) ^ 2 * ‖regressor‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring

end SimpleRegression

section FWL

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

/-- **Frisch–Waugh–Lovell theorem.** Provided the regressor of interest is not contained in the
nuisance subspace, the coefficient satisfying the joint profiled normal equation is exactly the
coefficient from regressing residualized outcome on residualized regressor. -/
theorem frischWaughLovell {regressor outcome : E}
    (hregressor : residualize U regressor ≠ 0) (β : ℝ) :
    inner ℝ regressor (profiledResidual U regressor outcome β) = 0 ↔
      β = partialRegressionCoefficient U regressor outcome := by
  rw [inner_regressor_profiledResidual_eq_inner_residualized,
    profiledResidual_eq_residualized, partialRegressionCoefficient]
  exact simpleRegression_normalEquation_iff hregressor β

/-- The FWL coefficient is the coefficient of any joint least-squares solution expressed through
the normal equations. -/
theorem coefficient_eq_partial_of_joint_normalEquations {regressor outcome nuisanceFit : E}
    {β : ℝ} (hregressor : residualize U regressor ≠ 0) (hnuisanceFit : nuisanceFit ∈ U)
    (hnuisanceNormal : ∀ nuisance ∈ U,
      inner ℝ (outcome - (nuisanceFit + β • regressor)) nuisance = 0)
    (hregressorNormal :
      inner ℝ regressor (outcome - (nuisanceFit + β • regressor)) = 0) :
    β = partialRegressionCoefficient U regressor outcome := by
  have hprojection : U.starProjection (outcome - β • regressor) = nuisanceFit := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hnuisanceFit ?_
    intro nuisance hnuisance
    have hresidual : outcome - β • regressor - nuisanceFit =
        outcome - (nuisanceFit + β • regressor) := by
      abel
    rw [hresidual]
    exact hnuisanceNormal nuisance hnuisance
  apply (frischWaughLovell U hregressor β).mp
  rw [profiledResidual, profiledNuisanceFit, hprojection]
  exact hregressorNormal

/-- Exact FWL loss decomposition. It strengthens the coefficient identity by describing the whole
profiled least-squares objective. -/
theorem frischWaughLovell_squaredError_decomposition {regressor outcome : E}
    (hregressor : residualize U regressor ≠ 0) (β : ℝ) :
    profiledSquaredError U regressor outcome β =
      profiledSquaredError U regressor outcome
          (partialRegressionCoefficient U regressor outcome) +
        (β - partialRegressionCoefficient U regressor outcome) ^ 2 *
          ‖residualize U regressor‖ ^ 2 := by
  unfold profiledSquaredError
  rw [profiledResidual_eq_residualized, profiledResidual_eq_residualized,
    partialRegressionCoefficient]
  exact simpleRegression_squaredError_decomposition hregressor β

/-- The residualized-regression coefficient globally minimizes the profiled joint squared error. -/
theorem partialRegressionCoefficient_minimal {regressor outcome : E}
    (hregressor : residualize U regressor ≠ 0) (β : ℝ) :
    profiledSquaredError U regressor outcome
        (partialRegressionCoefficient U regressor outcome) ≤
      profiledSquaredError U regressor outcome β := by
  have hdecomposition :=
    frischWaughLovell_squaredError_decomposition (outcome := outcome) U hregressor β
  calc
    profiledSquaredError U regressor outcome
        (partialRegressionCoefficient U regressor outcome) ≤
        profiledSquaredError U regressor outcome
            (partialRegressionCoefficient U regressor outcome) +
          (β - partialRegressionCoefficient U regressor outcome) ^ 2 *
            ‖residualize U regressor‖ ^ 2 :=
      le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = profiledSquaredError U regressor outcome β := hdecomposition.symm

/-- The FWL coefficient is the unique minimizer of the profiled joint squared error. -/
theorem partialRegressionCoefficient_unique {regressor outcome : E}
    (hregressor : residualize U regressor ≠ 0) {β : ℝ}
    (hoptimal : profiledSquaredError U regressor outcome β =
      profiledSquaredError U regressor outcome
        (partialRegressionCoefficient U regressor outcome)) :
    β = partialRegressionCoefficient U regressor outcome := by
  have hdecomposition :=
    frischWaughLovell_squaredError_decomposition (outcome := outcome) U hregressor β
  rw [hoptimal] at hdecomposition
  have hproduct :
      (β - partialRegressionCoefficient U regressor outcome) ^ 2 *
        ‖residualize U regressor‖ ^ 2 = 0 := by
    linarith
  have hnorm : ‖residualize U regressor‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hregressor)
  have hcoefficient :
      (β - partialRegressionCoefficient U regressor outcome) ^ 2 = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right hnorm
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hcoefficient)

end FWL

end Scalar

section Vector

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι]

/-- The linear fitted-value map produced by a finite family of regressors. -/
def vectorFittedValue (regressors : ι → E) : (ι → ℝ) →ₗ[ℝ] E :=
  Fintype.linearCombination ℝ regressors

/-- Residualize every member of a finite regressor family against `U`. -/
def residualizedRegressors (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressors : ι → E) : ι → E :=
  fun i ↦ residualize U (regressors i)

/-- For fixed coefficients, the optimal nuisance fit in the vector-regressor problem. -/
def vectorProfiledNuisanceFit (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressors : ι → E) (outcome : E) (coefficients : ι → ℝ) : E :=
  U.starProjection (outcome - vectorFittedValue regressors coefficients)

/-- The joint residual after optimizing the nuisance component at fixed vector coefficients. -/
def vectorProfiledResidual (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressors : ι → E) (outcome : E) (coefficients : ι → ℝ) : E :=
  outcome -
    (vectorProfiledNuisanceFit U regressors outcome coefficients +
      vectorFittedValue regressors coefficients)

/-- The joint squared-error objective after profiling out the nuisance coefficients. -/
def vectorProfiledSquaredError (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressors : ι → E) (outcome : E) (coefficients : ι → ℝ) : ℝ :=
  ‖vectorProfiledResidual U regressors outcome coefficients‖ ^ 2

/-- The Gram matrix of the regressors after residualizing them against `U`. -/
def residualizedGramMatrix (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressors : ι → E) : Matrix ι ι ℝ :=
  Matrix.gram ℝ (residualizedRegressors U regressors)

/-- Inner products of the residualized regressors with the residualized outcome. -/
def residualizedCrossMoment (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressors : ι → E) (outcome : E) : ι → ℝ :=
  fun i ↦ inner ℝ (residualize U (regressors i)) (residualize U outcome)

/-- The vector FWL coefficient, computed by the inverse residualized Gram matrix.  Theorems using
this definition impose nonsingularity of the Gram matrix. -/
def vectorPartialRegressionCoefficient [DecidableEq ι]
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (regressors : ι → E) (outcome : E) : ι → ℝ :=
  (residualizedGramMatrix U regressors)⁻¹.mulVec
    (residualizedCrossMoment U regressors outcome)

section Algebra

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

theorem residualize_sub (left right : E) :
    residualize U (left - right) = residualize U left - residualize U right := by
  exact map_sub (residualize U) left right

theorem residualize_vectorFittedValue (regressors : ι → E) (coefficients : ι → ℝ) :
    residualize U (vectorFittedValue regressors coefficients) =
      vectorFittedValue (residualizedRegressors U regressors) coefficients := by
  simp only [vectorFittedValue, Fintype.linearCombination_apply, residualizedRegressors,
    map_sum, map_smul]

theorem residualize_sub_vectorFittedValue (regressors : ι → E) (outcome : E)
    (coefficients : ι → ℝ) :
    residualize U (outcome - vectorFittedValue regressors coefficients) =
      residualize U outcome -
        vectorFittedValue (residualizedRegressors U regressors) coefficients := by
  rw [residualize_sub, residualize_vectorFittedValue]

theorem vectorProfiledNuisanceFit_mem (regressors : ι → E) (outcome : E)
    (coefficients : ι → ℝ) :
    vectorProfiledNuisanceFit U regressors outcome coefficients ∈ U := by
  exact Submodule.starProjection_apply_mem U _

/-- Profiling out the nuisance component is exactly residualizing the remaining vector-regression
problem. -/
theorem vectorProfiledResidual_eq_residualize (regressors : ι → E) (outcome : E)
    (coefficients : ι → ℝ) :
    vectorProfiledResidual U regressors outcome coefficients =
      residualize U (outcome - vectorFittedValue regressors coefficients) := by
  simp only [vectorProfiledResidual, vectorProfiledNuisanceFit, residualize_apply]
  abel

/-- The algebraic heart of vector FWL: residualize the outcome and every regressor, then run the
same vector regression. -/
theorem vectorProfiledResidual_eq_residualized (regressors : ι → E) (outcome : E)
    (coefficients : ι → ℝ) :
    vectorProfiledResidual U regressors outcome coefficients =
      residualize U outcome -
        vectorFittedValue (residualizedRegressors U regressors) coefficients := by
  rw [vectorProfiledResidual_eq_residualize, residualize_sub_vectorFittedValue]

theorem vectorProfiledResidual_mem_orthogonal (regressors : ι → E) (outcome : E)
    (coefficients : ι → ℝ) :
    vectorProfiledResidual U regressors outcome coefficients ∈ Uᗮ := by
  rw [vectorProfiledResidual_eq_residualize]
  exact residualize_mem_orthogonal U _

/-- Against a profiled residual, an original regressor and its residualization have the same inner
product. -/
theorem inner_regressor_vectorProfiledResidual_eq_inner_residualized
    (regressors : ι → E) (outcome : E) (coefficients : ι → ℝ) (i : ι) :
    inner ℝ (regressors i) (vectorProfiledResidual U regressors outcome coefficients) =
      inner ℝ (residualize U (regressors i))
        (vectorProfiledResidual U regressors outcome coefficients) := by
  have horthogonal :=
    vectorProfiledResidual_mem_orthogonal U regressors outcome coefficients
  have hprojection :
      inner ℝ (U.starProjection (regressors i))
        (vectorProfiledResidual U regressors outcome coefficients) = 0 :=
    horthogonal _ (Submodule.starProjection_apply_mem U (regressors i))
  rw [← sub_eq_zero, ← inner_sub_left]
  have hdifference :
      regressors i - residualize U (regressors i) = U.starProjection (regressors i) := by
    simp [residualize]
  rw [hdifference]
  exact hprojection

/-- Exact Pythagorean decomposition showing that `vectorProfiledNuisanceFit` really is the
least-squares nuisance fit for the fixed coefficient vector. -/
theorem vectorNuisanceFit_squaredError_decomposition
    (regressors : ι → E) (outcome : E) (coefficients : ι → ℝ)
    {nuisanceFit : E} (hnuisanceFit : nuisanceFit ∈ U) :
    ‖outcome - (nuisanceFit + vectorFittedValue regressors coefficients)‖ ^ 2 =
      vectorProfiledSquaredError U regressors outcome coefficients +
        ‖vectorProfiledNuisanceFit U regressors outcome coefficients - nuisanceFit‖ ^ 2 := by
  have hprofiledOrthogonal :=
    vectorProfiledResidual_mem_orthogonal U regressors outcome coefficients
  have hnuisanceDifference :
      vectorProfiledNuisanceFit U regressors outcome coefficients - nuisanceFit ∈ U :=
    U.sub_mem (vectorProfiledNuisanceFit_mem U regressors outcome coefficients) hnuisanceFit
  have horthogonal :
      inner ℝ (vectorProfiledResidual U regressors outcome coefficients)
        (vectorProfiledNuisanceFit U regressors outcome coefficients - nuisanceFit) = 0 := by
    rw [real_inner_comm]
    exact hprofiledOrthogonal _ hnuisanceDifference
  have hsplit :
      outcome - (nuisanceFit + vectorFittedValue regressors coefficients) =
        vectorProfiledResidual U regressors outcome coefficients +
          (vectorProfiledNuisanceFit U regressors outcome coefficients - nuisanceFit) := by
    unfold vectorProfiledResidual
    abel
  rw [hsplit, vectorProfiledSquaredError]
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthogonal

/-- Profiling the nuisance component minimizes squared error among all nuisance fits in `U`. -/
theorem vectorProfiledNuisanceFit_minimal
    (regressors : ι → E) (outcome : E) (coefficients : ι → ℝ)
    {nuisanceFit : E} (hnuisanceFit : nuisanceFit ∈ U) :
    vectorProfiledSquaredError U regressors outcome coefficients ≤
      ‖outcome - (nuisanceFit + vectorFittedValue regressors coefficients)‖ ^ 2 := by
  rw [vectorNuisanceFit_squaredError_decomposition U regressors outcome coefficients
    hnuisanceFit]
  exact le_add_of_nonneg_right (sq_nonneg _)

end Algebra

section NormalEquations

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

/-- **Rank-free vector FWL.** The joint profiled normal equations are exactly the normal equations
obtained after residualizing the outcome and every regressor.  This theorem remains valid for a
collinear regressor family. -/
theorem vectorFrischWaughLovell_normalEquations
    (regressors : ι → E) (outcome : E) (coefficients : ι → ℝ) :
    (∀ i, inner ℝ (regressors i)
        (vectorProfiledResidual U regressors outcome coefficients) = 0) ↔
      ∀ i, inner ℝ (residualize U (regressors i))
        (residualize U outcome -
          vectorFittedValue (residualizedRegressors U regressors) coefficients) = 0 := by
  constructor
  · intro h i
    rw [← vectorProfiledResidual_eq_residualized]
    rw [← inner_regressor_vectorProfiledResidual_eq_inner_residualized]
    exact h i
  · intro h i
    rw [inner_regressor_vectorProfiledResidual_eq_inner_residualized,
      vectorProfiledResidual_eq_residualized]
    exact h i

/-- The residualized normal equations in their usual Gram-matrix form `G β = Xᵀy`. -/
theorem vectorFrischWaughLovell_gramEquation
    (regressors : ι → E) (outcome : E) (coefficients : ι → ℝ) :
    (∀ i, inner ℝ (regressors i)
        (vectorProfiledResidual U regressors outcome coefficients) = 0) ↔
      (residualizedGramMatrix U regressors).mulVec coefficients =
        residualizedCrossMoment U regressors outcome := by
  rw [vectorFrischWaughLovell_normalEquations]
  constructor
  · intro h
    funext i
    have hi := h i
    rw [inner_sub_right, vectorFittedValue, Fintype.linearCombination_apply, inner_sum] at hi
    simp only [real_inner_smul_right] at hi
    simp only [residualizedGramMatrix, residualizedCrossMoment, Matrix.mulVec,
      Matrix.gram_apply]
    calc
      ∑ j, inner ℝ (residualize U (regressors i))
          (residualize U (regressors j)) * coefficients j =
          ∑ j, coefficients j * inner ℝ (residualize U (regressors i))
            (residualize U (regressors j)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = inner ℝ (residualize U (regressors i)) (residualize U outcome) :=
        (sub_eq_zero.mp hi).symm
  · intro h i
    have hi := congrFun h i
    rw [inner_sub_right, vectorFittedValue, Fintype.linearCombination_apply, inner_sum]
    simp only [real_inner_smul_right]
    rw [sub_eq_zero]
    simp only [residualizedGramMatrix, residualizedCrossMoment, Matrix.mulVec,
      Matrix.gram_apply] at hi
    calc
      inner ℝ (residualize U (regressors i)) (residualize U outcome) =
          ∑ j, inner ℝ (residualize U (regressors i))
            (residualize U (regressors j)) * coefficients j := hi.symm
      _ = ∑ j, coefficients j * inner ℝ (residualize U (regressors i))
            (residualize U (regressors j)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring

variable [DecidableEq ι]

theorem vectorPartialRegressionCoefficient_gramEquation
    (regressors : ι → E) (outcome : E)
    (hfullRank : (residualizedGramMatrix U regressors).det ≠ 0) :
    (residualizedGramMatrix U regressors).mulVec
        (vectorPartialRegressionCoefficient U regressors outcome) =
      residualizedCrossMoment U regressors outcome := by
  unfold vectorPartialRegressionCoefficient
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hfullRank),
    Matrix.one_mulVec]

/-- **Vector Frisch–Waugh–Lovell theorem.** With full column rank after residualization, the
unique coefficient vector satisfying the joint normal equations is the inverse-Gram coefficient
computed from the residualized regression. -/
theorem vectorFrischWaughLovell
    (regressors : ι → E) (outcome : E)
    (hfullRank : (residualizedGramMatrix U regressors).det ≠ 0)
    (coefficients : ι → ℝ) :
    (∀ i, inner ℝ (regressors i)
        (vectorProfiledResidual U regressors outcome coefficients) = 0) ↔
      coefficients = vectorPartialRegressionCoefficient U regressors outcome := by
  rw [vectorFrischWaughLovell_gramEquation]
  constructor
  · intro h
    apply Matrix.mulVec_injective_of_det_ne_zero hfullRank
    rw [h]
    exact (vectorPartialRegressionCoefficient_gramEquation U regressors outcome hfullRank).symm
  · rintro rfl
    exact vectorPartialRegressionCoefficient_gramEquation U regressors outcome hfullRank

/-- Nonsingularity of the residualized Gram matrix is precisely linear independence of the
residualized regressor family. -/
theorem residualizedGramMatrix_det_ne_zero_iff
    (regressors : ι → E) :
    (residualizedGramMatrix U regressors).det ≠ 0 ↔
      LinearIndependent ℝ (residualizedRegressors U regressors) := by
  exact Matrix.det_gram_ne_zero_iff_linearIndependent

/-- The vector FWL coefficient is the coefficient vector of any joint least-squares solution
expressed through the nuisance and regressor normal equations. -/
theorem vectorCoefficient_eq_partial_of_joint_normalEquations
    (regressors : ι → E) (outcome : E)
    (hfullRank : (residualizedGramMatrix U regressors).det ≠ 0)
    {nuisanceFit : E} {coefficients : ι → ℝ}
    (hnuisanceFit : nuisanceFit ∈ U)
    (hnuisanceNormal : ∀ nuisance ∈ U,
      inner ℝ
        (outcome - (nuisanceFit + vectorFittedValue regressors coefficients)) nuisance = 0)
    (hregressorNormal : ∀ i,
      inner ℝ (regressors i)
        (outcome - (nuisanceFit + vectorFittedValue regressors coefficients)) = 0) :
    coefficients = vectorPartialRegressionCoefficient U regressors outcome := by
  have hprojection :
      U.starProjection (outcome - vectorFittedValue regressors coefficients) = nuisanceFit := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hnuisanceFit ?_
    intro nuisance hnuisance
    have hresidual :
        outcome - vectorFittedValue regressors coefficients - nuisanceFit =
          outcome - (nuisanceFit + vectorFittedValue regressors coefficients) := by
      abel
    rw [hresidual]
    exact hnuisanceNormal nuisance hnuisance
  apply (vectorFrischWaughLovell U regressors outcome hfullRank coefficients).mp
  intro i
  rw [vectorProfiledResidual, vectorProfiledNuisanceFit, hprojection]
  exact hregressorNormal i

end NormalEquations

section LeastSquares

variable [DecidableEq ι]
variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

/-- Exact loss decomposition for vector FWL.  The excess loss is the squared norm of the fitted
value produced by the coefficient error. -/
theorem vectorFrischWaughLovell_squaredError_decomposition
    (regressors : ι → E) (outcome : E)
    (hfullRank : (residualizedGramMatrix U regressors).det ≠ 0)
    (coefficients : ι → ℝ) :
    vectorProfiledSquaredError U regressors outcome coefficients =
      vectorProfiledSquaredError U regressors outcome
          (vectorPartialRegressionCoefficient U regressors outcome) +
        ‖vectorFittedValue (residualizedRegressors U regressors)
          (fun i ↦ vectorPartialRegressionCoefficient U regressors outcome i -
            coefficients i)‖ ^ 2 := by
  let coefficientsHat := vectorPartialRegressionCoefficient U regressors outcome
  have hnormalOriginal : ∀ i,
      inner ℝ (regressors i)
        (vectorProfiledResidual U regressors outcome coefficientsHat) = 0 :=
    (vectorFrischWaughLovell U regressors outcome hfullRank coefficientsHat).mpr rfl
  have hnormal (i : ι) :
      inner ℝ (residualize U (regressors i))
        (vectorProfiledResidual U regressors outcome coefficientsHat) = 0 := by
    rw [← inner_regressor_vectorProfiledResidual_eq_inner_residualized]
    exact hnormalOriginal i
  have horthogonal :
      inner ℝ (vectorProfiledResidual U regressors outcome coefficientsHat)
        (vectorFittedValue (residualizedRegressors U regressors)
          (fun i ↦ coefficientsHat i - coefficients i)) = 0 := by
    rw [vectorFittedValue, Fintype.linearCombination_apply, inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [real_inner_smul_right, real_inner_comm]
    simp [residualizedRegressors, hnormal]
  have hfitDifference :
      vectorFittedValue (residualizedRegressors U regressors)
          (fun i ↦ coefficientsHat i - coefficients i) =
      vectorFittedValue (residualizedRegressors U regressors) coefficientsHat -
          vectorFittedValue (residualizedRegressors U regressors) coefficients := by
    exact map_sub (vectorFittedValue (residualizedRegressors U regressors))
      coefficientsHat coefficients
  have hsplit :
      vectorProfiledResidual U regressors outcome coefficients =
        vectorProfiledResidual U regressors outcome coefficientsHat +
          vectorFittedValue (residualizedRegressors U regressors)
            (fun i ↦ coefficientsHat i - coefficients i) := by
    rw [vectorProfiledResidual_eq_residualized,
      vectorProfiledResidual_eq_residualized]
    rw [hfitDifference]
    abel
  unfold vectorProfiledSquaredError
  rw [hsplit]
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthogonal

/-- The inverse-Gram vector FWL coefficient globally minimizes the profiled joint squared error. -/
theorem vectorPartialRegressionCoefficient_minimal
    (regressors : ι → E) (outcome : E)
    (hfullRank : (residualizedGramMatrix U regressors).det ≠ 0)
    (coefficients : ι → ℝ) :
    vectorProfiledSquaredError U regressors outcome
        (vectorPartialRegressionCoefficient U regressors outcome) ≤
      vectorProfiledSquaredError U regressors outcome coefficients := by
  rw [vectorFrischWaughLovell_squaredError_decomposition U regressors outcome hfullRank
    coefficients]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- With full residualized column rank, the vector FWL coefficient is the unique minimizer of the
profiled squared-error objective. -/
theorem vectorPartialRegressionCoefficient_unique
    (regressors : ι → E) (outcome : E)
    (hfullRank : (residualizedGramMatrix U regressors).det ≠ 0)
    {coefficients : ι → ℝ}
    (hoptimal :
      vectorProfiledSquaredError U regressors outcome coefficients =
        vectorProfiledSquaredError U regressors outcome
          (vectorPartialRegressionCoefficient U regressors outcome)) :
    coefficients = vectorPartialRegressionCoefficient U regressors outcome := by
  let coefficientsHat := vectorPartialRegressionCoefficient U regressors outcome
  have hdecomposition :=
    vectorFrischWaughLovell_squaredError_decomposition U regressors outcome hfullRank coefficients
  change vectorProfiledSquaredError U regressors outcome coefficients =
      vectorProfiledSquaredError U regressors outcome coefficientsHat at hoptimal
  change vectorProfiledSquaredError U regressors outcome coefficients =
      vectorProfiledSquaredError U regressors outcome coefficientsHat +
        ‖vectorFittedValue (residualizedRegressors U regressors)
          (fun i ↦ coefficientsHat i - coefficients i)‖ ^ 2 at hdecomposition
  rw [hoptimal] at hdecomposition
  have hnorm :
      ‖vectorFittedValue (residualizedRegressors U regressors)
        (fun i ↦ coefficientsHat i - coefficients i)‖ ^ 2 = 0 := by
    linarith
  have hfitted :
      vectorFittedValue (residualizedRegressors U regressors)
        (fun i ↦ coefficientsHat i - coefficients i) = 0 := by
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp hnorm
  have hlinearIndependent :
      LinearIndependent ℝ (residualizedRegressors U regressors) :=
    (residualizedGramMatrix_det_ne_zero_iff U regressors).mp hfullRank
  have hcoefficientZero : ∀ i, coefficientsHat i - coefficients i = 0 :=
    (Fintype.linearIndependent_iff.mp hlinearIndependent)
      (fun i ↦ coefficientsHat i - coefficients i) hfitted
  funext i
  exact (sub_eq_zero.mp (hcoefficientZero i)).symm

end LeastSquares

end Vector

section FixedDesignInterface

open scoped RealInnerProductSpace

variable {P O : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [FiniteDimensional ℝ P]
  [NormedAddCommGroup O] [InnerProductSpace ℝ O] [CompleteSpace O]

namespace FixedDesign

variable (D : FixedDesign P O)

/-- The concrete OLS residual-maker is exactly abstract residualization against the design
range.  This is an equality of continuous linear maps, so all linearity and pointwise corollaries
follow by coercion. -/
theorem residualMaker_eq_residualize :
    D.residualMaker = residualize D.map.range := by
  ext y
  rw [D.residualMaker_apply, residualize_apply, D.starProjection_eq_fitted]

@[simp, nolint simpNF]
theorem residualMaker_apply_eq_residualize (y : O) :
    D.residualMaker y = residualize D.map.range y := by
  rw [D.residualMaker_eq_residualize]

end FixedDesign

section PartitionedDesign

variable {Q ι : Type*}
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [FiniteDimensional ℝ Q]
  [Fintype ι] [DecidableEq ι]

/-- The Hilbert direct sum used for a nuisance block and a finite coefficient block. -/
abbrev PartitionedParameter (Q ι : Type*) :=
  WithLp 2 (Q × EuclideanSpace ℝ ι)

omit [CompleteSpace O] [CompleteSpace Q] in
/-- Full column rank of a partitioned design implies full column rank of the regressors after
residualizing against the nuisance-design range. -/
theorem residualizedGramMatrix_det_ne_zero_of_partitionedDesign
    (N : FixedDesign Q O) (J : FixedDesign (PartitionedParameter Q ι) O)
    (regressors : ι → O)
    (hpartition : ∀ q b,
      J.map (WithLp.toLp 2 (q, b)) = N.map q + vectorFittedValue regressors b) :
    (residualizedGramMatrix N.map.range regressors).det ≠ 0 := by
  rw [residualizedGramMatrix_det_ne_zero_iff]
  refine Fintype.linearIndependent_iff.mpr ?_
  intro b hsum i
  have hresidualizedFit :
      residualize N.map.range (vectorFittedValue regressors b) = 0 := by
    rw [residualize_vectorFittedValue]
    simpa only [vectorFittedValue, Fintype.linearCombination_apply] using hsum
  have hfitMem : vectorFittedValue regressors b ∈ N.map.range :=
    (residualize_eq_zero_iff N.map.range _).mp hresidualizedFit
  obtain ⟨q, hq⟩ := hfitMem
  let bE : EuclideanSpace ℝ ι := WithLp.toLp 2 b
  have hjoint :
      J.map (WithLp.toLp 2 (q, 0)) = J.map (WithLp.toLp 2 (0, bE)) := by
    rw [hpartition, hpartition]
    change N.map q + vectorFittedValue regressors 0 =
      N.map 0 + vectorFittedValue regressors b
    simpa [vectorFittedValue] using hq
  have hpairs : WithLp.toLp 2 (q, 0) = WithLp.toLp 2 (0, bE) := J.injective hjoint
  have hi := congrArg (fun z : PartitionedParameter Q ι ↦ z.snd i) hpairs
  simpa [bE] using hi.symm

/-- **Partitioned-design vector FWL.** If the joint design map consists of a nuisance block and a
finite regressor block, then the second block of its OLS coefficient is exactly the coefficient
obtained by residualizing the outcome and the regressors against the nuisance-design range.

The required residualized full-rank condition is derived from injectivity of the joint design. -/
theorem partitionedOls_regressorBlock_eq_vectorPartialRegressionCoefficient
    (N : FixedDesign Q O) (J : FixedDesign (PartitionedParameter Q ι) O)
    (regressors : ι → O)
    (hpartition : ∀ q b,
      J.map (WithLp.toLp 2 (q, b)) = N.map q + vectorFittedValue regressors b)
    (outcome : O) :
    (J.ols outcome).snd =
      vectorPartialRegressionCoefficient N.map.range regressors outcome := by
  have hfullRank : (residualizedGramMatrix N.map.range regressors).det ≠ 0 :=
    residualizedGramMatrix_det_ne_zero_of_partitionedDesign N J regressors hpartition
  have hfit :
      N.map (J.ols outcome).fst + vectorFittedValue regressors (J.ols outcome).snd =
        J.fitted outcome := by
    calc
      N.map (J.ols outcome).fst + vectorFittedValue regressors (J.ols outcome).snd =
          J.map (J.ols outcome) :=
        (hpartition (J.ols outcome).fst (J.ols outcome).snd).symm
      _ = J.fitted outcome := rfl
  have hresidual :
      outcome - (N.map (J.ols outcome).fst +
        vectorFittedValue regressors (J.ols outcome).snd) = J.residualMaker outcome := by
    rw [hfit, J.residualMaker_apply]
  apply vectorCoefficient_eq_partial_of_joint_normalEquations
      N.map.range regressors outcome hfullRank
  · exact ⟨(J.ols outcome).fst, rfl⟩
  · intro nuisance hnuisance
    obtain ⟨q, rfl⟩ := hnuisance
    have hnuisanceJoint : N.map q ∈ J.map.range := by
      refine ⟨WithLp.toLp 2 (q, 0), ?_⟩
      simpa [vectorFittedValue] using hpartition q (0 : EuclideanSpace ℝ ι)
    calc
      inner ℝ
          (outcome - (N.map (J.ols outcome).fst +
            vectorFittedValue regressors (J.ols outcome).snd)) (N.map q) =
          inner ℝ (J.residualMaker outcome) (N.map q) := by rw [hresidual]
      _ = 0 := by
        rw [real_inner_comm]
        exact J.residualMaker_mem_orthogonal outcome _ hnuisanceJoint
  · intro i
    have hregressorJoint : regressors i ∈ J.map.range := by
      let ei : EuclideanSpace ℝ ι := WithLp.toLp 2 (Pi.single i 1)
      refine ⟨WithLp.toLp 2 (0, ei), ?_⟩
      simpa [ei, vectorFittedValue] using hpartition (0 : Q) ei
    calc
      inner ℝ (regressors i)
          (outcome - (N.map (J.ols outcome).fst +
            vectorFittedValue regressors (J.ols outcome).snd)) =
          inner ℝ (regressors i) (J.residualMaker outcome) := by rw [hresidual]
      _ = 0 := by
        exact J.residualMaker_mem_orthogonal outcome _ hregressorJoint

end PartitionedDesign

end FixedDesignInterface

end

end LeanRegression
