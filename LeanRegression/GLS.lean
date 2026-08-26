import LeanRegression.GaussMarkov

set_option linter.style.header false

/-!
# Generalized least squares and Aitken's theorem

A positive-definite covariance is represented by an invertible whitening map whose pushforward
error law has spherical covariance with positive scale.  GLS is OLS after whitening.  Applying the
Gauss–Markov theorem to the whitened model gives Aitken's exact covariance-gap identity and the
BLUE conclusion.
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

/-- Transform a fixed design by an invertible whitening operator. -/
def whiten (W : O ≃L[ℝ] O) : FixedDesign P O where
  map := W.toContinuousLinearMap ∘L D.map
  injective := W.injective.comp D.injective

omit [CompleteSpace P] [FiniteDimensional ℝ P]
  [CompleteSpace O] in
@[simp]
theorem whiten_map (W : O ≃L[ℝ] O) (β : P) :
    (D.whiten W).map β = W (D.map β) :=
  rfl

/-- Express an estimator of the original observations as an estimator of whitened observations. -/
def whitenEstimator (A : O →L[ℝ] P) (W : O ≃L[ℝ] O) : O →L[ℝ] P :=
  A ∘L W.symm.toContinuousLinearMap

omit [CompleteSpace P] [FiniteDimensional ℝ P]
  [CompleteSpace O] in
@[simp]
theorem whitenEstimator_apply (A : O →L[ℝ] P) (W : O ≃L[ℝ] O) (y : O) :
    whitenEstimator A W y = A (W.symm y) :=
  rfl

omit [CompleteSpace P] [FiniteDimensional ℝ P]
  [CompleteSpace O] in
theorem whitenEstimator_isLinearUnbiasedEstimator
    (A : O →L[ℝ] P) (hA : D.IsLinearUnbiasedEstimator A) (W : O ≃L[ℝ] O) :
    (D.whiten W).IsLinearUnbiasedEstimator (whitenEstimator A W) := by
  rw [(D.whiten W).isLinearUnbiasedEstimator_iff]
  intro β
  simp only [whitenEstimator_apply, whiten_map, W.symm_apply_apply]
  exact (D.isLinearUnbiasedEstimator_iff A).mp hA β

/-- Generalized least squares: whiten the observations, then apply OLS to the whitened design. -/
def gls (W : O ≃L[ℝ] O) : O →L[ℝ] P :=
  (D.whiten W).ols ∘L W.toContinuousLinearMap

@[simp]
theorem gls_apply (W : O ≃L[ℝ] O) (y : O) :
    D.gls W y = (D.whiten W).ols (W y) :=
  rfl

theorem gls_isLinearUnbiasedEstimator (W : O ≃L[ℝ] O) :
    D.IsLinearUnbiasedEstimator (D.gls W) := by
  rw [D.isLinearUnbiasedEstimator_iff]
  intro β
  change (D.whiten W).ols ((D.whiten W).map β) = β
  exact (D.whiten W).ols_map β

theorem whitenEstimator_gls (W : O ≃L[ℝ] O) :
    whitenEstimator (D.gls W) W = (D.whiten W).ols := by
  ext y
  simp [whitenEstimator, gls]

/-- Postcomposing a whitening map with an orthogonal change of coordinates does not change GLS.
Thus the estimator is independent of the particular whitening coordinates whenever two
whitenings differ by a linear isometry equivalence. -/
theorem gls_trans_linearIsometryEquiv (W : O ≃L[ℝ] O) (Q : O ≃ₗᵢ[ℝ] O) :
    D.gls (W.trans Q.toContinuousLinearEquiv) = D.gls W := by
  let WQ := W.trans Q.toContinuousLinearEquiv
  let DWQ := D.whiten WQ
  let DW := D.whiten W
  have hgram : DWQ.gram = DW.gram := by
    ext p
    apply ext_inner_right ℝ
    intro r
    simp only [FixedDesign.gram, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    exact Q.inner_map_map (W (D.map p)) (W (D.map r))
  have hcross (y : O) : DWQ.map.adjoint (WQ y) = DW.map.adjoint (W y) := by
    apply ext_inner_right ℝ
    intro p
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    exact Q.inner_map_map (W y) (W (D.map p))
  have hinverse (x : P) : DWQ.gramInverse x = DW.gramInverse x := by
    apply DW.gram_injective
    rw [DW.gram_apply_gramInverse, ← hgram, DWQ.gram_apply_gramInverse]
  ext y
  change DWQ.gramInverse (DWQ.map.adjoint (WQ y)) =
    DW.gramInverse (DW.map.adjoint (W y))
  rw [hcross, hinverse]

omit [FiniteDimensional ℝ P] in
theorem whitening_adjoint_whitenEstimator
    (A : O →L[ℝ] P) (W : O ≃L[ℝ] O) (u : P) :
    W.toContinuousLinearMap.adjoint ((whitenEstimator A W).adjoint u) = A.adjoint u := by
  calc
    W.toContinuousLinearMap.adjoint ((whitenEstimator A W).adjoint u) =
        (whitenEstimator A W ∘L W.toContinuousLinearMap).adjoint u := by
          rw [ContinuousLinearMap.adjoint_comp]
          rfl
    _ = A.adjoint u := by
      have hcomp : whitenEstimator A W ∘L W.toContinuousLinearMap = A := by
        ext y
        simp [whitenEstimator]
      rw [hcomp]

omit [FiniteDimensional ℝ P] in
/-- Covariance is unchanged when both the observations and estimator are transformed by mutually
inverse whitening maps. -/
theorem estimatorCovariance_whitened
    [MeasurableSpace O] [BorelSpace O] [SecondCountableTopology O]
    {μ : Measure O} [IsFiniteMeasure μ] (hμ : MemLp id 2 μ)
    (A : O →L[ℝ] P) (W : O ≃L[ℝ] O) :
    estimatorCovariance (μ.map W) (whitenEstimator A W) =
      estimatorCovariance μ A := by
  ext u v
  rw [estimatorCovariance_apply, estimatorCovariance_apply]
  change covarianceBilin (μ.map W.toContinuousLinearMap)
      ((whitenEstimator A W).adjoint u) ((whitenEstimator A W).adjoint v) = _
  rw [covarianceBilin_map hμ, whitening_adjoint_whitenEstimator,
    whitening_adjoint_whitenEstimator]

end FixedDesign

/-- An operational whitening hypothesis for a square-integrable error law.  It records an
invertible bounded map under which covariance is `varianceScale • innerSL ℝ`, with positive
scale.  In finite dimensions this is the usual representation of positive-definite covariance;
in infinite dimensions the existence of a bounded invertible whitening map is a stronger
assumption than mere injective positivity of a covariance operator. -/
structure PositiveDefiniteNoise (O : Type*)
    [NormedAddCommGroup O] [InnerProductSpace ℝ O] [CompleteSpace O]
    [MeasurableSpace O] [BorelSpace O]
    (μ : Measure O) where
  /-- The positive spherical variance after whitening. -/
  varianceScale : ℝ
  varianceScale_pos : 0 < varianceScale
  /-- An inverse square-root covariance transform. -/
  whitening : O ≃L[ℝ] O
  memLp_two : MemLp id 2 μ
  covariance_whitened :
    IsIsotropicCovariance (μ.map whitening) varianceScale

namespace FixedDesign

variable (D : FixedDesign P O)
variable [MeasurableSpace O] [BorelSpace O] [SecondCountableTopology O]

/-- **Aitken's exact covariance-gap identity.** -/
theorem aitken_estimatorCovariance_gap
    {μ : Measure O} [IsFiniteMeasure μ] (N : PositiveDefiniteNoise O μ)
    (A : O →L[ℝ] P) (hA : D.IsLinearUnbiasedEstimator A) (u : P) :
    estimatorCovariance μ A u u =
      estimatorCovariance μ (D.gls N.whitening) u u +
        N.varianceScale *
          ‖(whitenEstimator A N.whitening - (D.whiten N.whitening).ols).adjoint u‖ ^ 2 := by
  let DW := D.whiten N.whitening
  let AW := whitenEstimator A N.whitening
  have hAW : DW.IsLinearUnbiasedEstimator AW :=
    D.whitenEstimator_isLinearUnbiasedEstimator A hA N.whitening
  have hgap :=
    DW.gaussMarkov_estimatorCovariance_gap N.covariance_whitened AW hAW u
  have hAtransport := estimatorCovariance_whitened N.memLp_two A N.whitening
  have hGLStransport :=
    estimatorCovariance_whitened N.memLp_two (D.gls N.whitening) N.whitening
  rw [D.whitenEstimator_gls] at hGLStransport
  calc
    estimatorCovariance μ A u u = estimatorCovariance (μ.map N.whitening) AW u u := by
      rw [hAtransport]
    _ = estimatorCovariance (μ.map N.whitening) DW.ols u u +
        N.varianceScale * ‖(AW - DW.ols).adjoint u‖ ^ 2 := hgap
    _ = estimatorCovariance μ (D.gls N.whitening) u u +
        N.varianceScale * ‖(AW - DW.ols).adjoint u‖ ^ 2 := by
      rw [hGLStransport]

/-- **Aitken–GLS theorem.** GLS is BLUE under a positive-definite covariance admitting the stated
whitening transform. -/
theorem aitken_gls_blue
    {μ : Measure O} [IsFiniteMeasure μ] (N : PositiveDefiniteNoise O μ)
    (A : O →L[ℝ] P) (hA : D.IsLinearUnbiasedEstimator A) :
    (estimatorCovariance μ A -
      estimatorCovariance μ (D.gls N.whitening)).toBilinForm.IsPosSemidef := by
  refine ⟨estimatorCovariance_sub_isSymm μ A (D.gls N.whitening), ⟨fun u ↦ ?_⟩⟩
  simp only [ContinuousLinearMap.toBilinForm_apply, sub_apply]
  have hgap := D.aitken_estimatorCovariance_gap N A hA u
  rw [hgap]
  simpa only [add_sub_cancel_left] using
    mul_nonneg N.varianceScale_pos.le
      (sq_nonneg ‖(whitenEstimator A N.whitening -
        (D.whiten N.whitening).ols).adjoint u‖)

end FixedDesign

end

end LeanRegression

