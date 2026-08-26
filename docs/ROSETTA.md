# Rosetta table

| Lean declaration | Textbook notation | One-line English |
|---|---|---|
| `LeanRegression.FixedDesign.map` | `X : ℝᵏ → ℝⁿ` | The fixed design sends coefficients to fitted observations. |
| `LeanRegression.FixedDesign.gram` | `XᵀX` | The Gram operator measures design geometry in parameter space. |
| `LeanRegression.FixedDesign.ols` | `(XᵀX)⁻¹Xᵀ` | The ordinary least-squares estimator. |
| `LeanRegression.residualize U` | `M_U = I - P_U` | Remove the orthogonal projection onto nuisance regressors. |
| `LeanRegression.partialRegressionCoefficient` | `(xᵀM_Ux)⁻¹xᵀM_Uy` | The scalar coefficient after residualizing regressor and outcome. |
| `LeanRegression.vectorPartialRegressionCoefficient` | `(X₂ᵀM₁X₂)⁻¹X₂ᵀM₁y` | The vector coefficient from residualized multiple regression. |
| `LeanRegression.FixedDesign.responseLaw μ β` | `Law(Xβ + ε)` | The observation distribution at parameter `β`. |
| `LeanRegression.IsIsotropicCovariance μ σ²` | `Cov(ε) = σ²I` | Every orthogonal direction is uncorrelated and has the same variance scale. |
| `LeanRegression.estimatorCovariance μ A` | `A Σ Aᵀ` | The covariance form of the linear estimator `Ay`. |
| `ContinuousLinearMap.toBilinForm.IsPosSemidef` | `⪰ 0` | The covariance difference is nonnegative in every parameter direction. |
