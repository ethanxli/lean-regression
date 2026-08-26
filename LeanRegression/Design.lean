import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.style.header false

/-!
# Fixed-design least squares

This module provides a coordinate-free API for finite-dimensional, full-column-rank fixed-design
regression.  A design is a continuous linear map from the parameter space to the observation
space, together with injectivity.  The OLS map is constructed from the inverse Gram operator.
-/

namespace LeanRegression

noncomputable section

open scoped RealInnerProductSpace

variable {P O : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [FiniteDimensional ℝ P]
  [NormedAddCommGroup O] [InnerProductSpace ℝ O] [CompleteSpace O]

/-- A finite-dimensional fixed design with full column rank. -/
structure FixedDesign (P O : Type*)
    [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [NormedAddCommGroup O] [InnerProductSpace ℝ O] where
  /-- The map from coefficients to fitted observations. -/
  map : P →L[ℝ] O
  /-- Full column rank. -/
  injective : Function.Injective map

namespace FixedDesign

variable (D : FixedDesign P O)

/-- The range of a finite-dimensional design admits an orthogonal projection, even when the
observation space itself is infinite-dimensional. -/
noncomputable instance mapRangeHasOrthogonalProjection :
    D.map.range.HasOrthogonalProjection := by
  let : CompleteSpace D.map.range := FiniteDimensional.complete ℝ D.map.range
  infer_instance

/-- The Gram operator `X†X`. -/
def gram : P →L[ℝ] P :=
  D.map.adjoint ∘L D.map

omit [FiniteDimensional ℝ P] in
theorem gram_ker : D.gram.ker = ⊥ := by
  rw [gram, ContinuousLinearMap.ker_adjoint_comp_self]
  exact LinearMap.ker_eq_bot.mpr D.injective

omit [FiniteDimensional ℝ P] in
theorem gram_injective : Function.Injective D.gram :=
  LinearMap.ker_eq_bot.mp D.gram_ker

theorem gram_surjective : Function.Surjective D.gram :=
  LinearMap.injective_iff_surjective.mp D.gram_injective

theorem gram_range : D.gram.range = ⊤ :=
  LinearMap.range_eq_top.mpr D.gram_surjective

/-- The Gram operator as a continuous linear equivalence. -/
def gramEquiv : P ≃L[ℝ] P :=
  ContinuousLinearEquiv.ofBijective D.gram D.gram_ker D.gram_range

/-- The inverse Gram operator `(X†X)⁻¹`. -/
def gramInverse : P →L[ℝ] P :=
  D.gramEquiv.symm.toContinuousLinearMap

@[simp]
theorem gram_apply_gramInverse (x : P) : D.gram (D.gramInverse x) = x :=
  D.gramEquiv.apply_symm_apply x

@[simp]
theorem gramInverse_apply_gram (x : P) : D.gramInverse (D.gram x) = x :=
  D.gramEquiv.symm_apply_apply x

omit [FiniteDimensional ℝ P] in
theorem gram_isSymmetric : (D.gram : P →ₗ[ℝ] P).IsSymmetric := by
  intro x y
  simp [gram, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

theorem gramInverse_isSymmetric : (D.gramInverse : P →ₗ[ℝ] P).IsSymmetric := by
  intro x y
  calc
    inner ℝ (D.gramInverse x) y =
        inner ℝ (D.gramInverse x) (D.gram (D.gramInverse y)) := by
          rw [D.gram_apply_gramInverse]
    _ = inner ℝ (D.gram (D.gramInverse x)) (D.gramInverse y) :=
      (D.gram_isSymmetric (D.gramInverse x) (D.gramInverse y)).symm
    _ = inner ℝ x (D.gramInverse y) := by
      rw [D.gram_apply_gramInverse]

@[simp]
theorem gramInverse_adjoint : D.gramInverse.adjoint = D.gramInverse :=
  D.gramInverse_isSymmetric.clm_adjoint_eq

/-- The ordinary least-squares coefficient map `(X†X)⁻¹X†`. -/
def ols : O →L[ℝ] P :=
  D.gramInverse ∘L D.map.adjoint

@[simp]
theorem ols_apply (y : O) : D.ols y = D.gramInverse (D.map.adjoint y) :=
  rfl

/-- OLS is a left inverse of a full-column-rank design. -/
theorem ols_comp_map : D.ols ∘L D.map = ContinuousLinearMap.id ℝ P := by
  ext x
  exact D.gramInverse_apply_gram x

@[simp, nolint simpNF]
theorem ols_map (x : P) : D.ols (D.map x) = x := by
  exact D.gramInverse_apply_gram x

@[simp]
theorem ols_adjoint : D.ols.adjoint = D.map ∘L D.gramInverse := by
  rw [ols, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    D.gramInverse_adjoint]

/-- The OLS fitted-value operator. -/
def fitted : O →L[ℝ] O :=
  D.map ∘L D.ols

/-- The OLS residual-maker operator. -/
def residualMaker : O →L[ℝ] O :=
  ContinuousLinearMap.id ℝ O - D.fitted

@[simp]
theorem fitted_apply (y : O) : D.fitted y = D.map (D.ols y) :=
  rfl

@[simp]
theorem residualMaker_apply (y : O) : D.residualMaker y = y - D.fitted y :=
  rfl

theorem fitted_mem_range (y : O) : D.fitted y ∈ D.map.range :=
  ⟨D.ols y, rfl⟩

theorem map_adjoint_residualMaker (y : O) :
    D.map.adjoint (D.residualMaker y) = 0 := by
  rw [D.residualMaker_apply, map_sub, D.fitted_apply]
  change D.map.adjoint y - D.gram (D.gramInverse (D.map.adjoint y)) = 0
  rw [D.gram_apply_gramInverse, sub_self]

theorem residualMaker_mem_orthogonal (y : O) :
    D.residualMaker y ∈ D.map.rangeᗮ := by
  rw [ContinuousLinearMap.orthogonal_range]
  exact D.map_adjoint_residualMaker y

theorem fitted_idempotent : D.fitted ∘L D.fitted = D.fitted := by
  ext y
  simp [fitted, D.ols_map]

/-- Exact least-squares loss decomposition for the OLS coefficient. -/
theorem ols_squaredError_decomposition (y : O) (β : P) :
    ‖y - D.map β‖ ^ 2 =
      ‖D.residualMaker y‖ ^ 2 + ‖D.map (D.ols y - β)‖ ^ 2 := by
  have horthogonal :
      inner ℝ (D.residualMaker y) (D.map (D.ols y - β)) = 0 := by
    rw [real_inner_comm]
    exact D.residualMaker_mem_orthogonal y _ ⟨D.ols y - β, rfl⟩
  have hsplit :
      y - D.map β = D.residualMaker y + D.map (D.ols y - β) := by
    simp only [D.residualMaker_apply, D.fitted_apply, map_sub]
    abel
  rw [hsplit]
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthogonal

/-- OLS globally minimizes squared residual norm. -/
theorem ols_minimal (y : O) (β : P) :
    ‖D.residualMaker y‖ ^ 2 ≤ ‖y - D.map β‖ ^ 2 := by
  rw [D.ols_squaredError_decomposition]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Full column rank makes the OLS coefficient the unique least-squares minimizer. -/
theorem ols_unique (y : O) {β : P}
    (hoptimal : ‖y - D.map β‖ ^ 2 = ‖D.residualMaker y‖ ^ 2) :
    β = D.ols y := by
  have hdecomp := D.ols_squaredError_decomposition y β
  rw [hoptimal] at hdecomp
  have hzero : ‖D.map (D.ols y - β)‖ = 0 := by
    apply sq_eq_zero_iff.mp
    linarith
  have hmap : D.map (D.ols y - β) = D.map 0 := by
    simpa using norm_eq_zero.mp hzero
  have : D.ols y - β = 0 := D.injective hmap
  exact (sub_eq_zero.mp this).symm

/-- OLS fitted values are the orthogonal projection onto the design range. -/
theorem starProjection_eq_fitted (y : O) :
    D.map.range.starProjection y = D.fitted y := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (D.fitted_mem_range y) ?_
  intro z hz
  rw [real_inner_comm]
  exact D.residualMaker_mem_orthogonal y z hz

end FixedDesign

end

end LeanRegression
