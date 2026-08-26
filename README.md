# Lean Regression

[![CI](https://github.com/ethanxli/lean-regression/actions/workflows/ci.yml/badge.svg)](https://github.com/ethanxli/lean-regression/actions/workflows/ci.yml)
[![Mathlib master](https://github.com/ethanxli/lean-regression/actions/workflows/mathlib-master.yml/badge.svg)](https://github.com/ethanxli/lean-regression/actions/workflows/mathlib-master.yml)
[![Blueprint](https://img.shields.io/badge/read-the%20blueprint-4051b5)](https://ethanxli.github.io/lean-regression/blueprint/)
[![API](https://img.shields.io/badge/browse-Lean%20API-0f7b6c)](https://ethanxli.github.io/lean-regression/docs/)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

`LeanRegression` is a small, auditable Lean 4 library for the linear-algebraic and probability
foundations of regression. It formalizes ordinary least squares, scalar and vector
Frisch–Waugh–Lovell, Gauss–Markov in Loewner order, generalized least squares/Aitken, and the
conditional-expectation minimum-MSE theorem.

The library is coordinate-free: finite-dimensional real Hilbert spaces replace a hard-coded
matrix representation. The headline Gauss–Markov theorem explicitly separates centered errors
from isotropic covariance, states unbiasedness for every parameter value, and compares full
covariance forms—not merely coordinate variances.

## Read before reading Lean

- [Blueprint](https://ethanxli.github.io/lean-regression/blueprint/): theorem statements, proof
  skeleton, and dependency graph; each formalized node links to its Lean API declaration.
- [Printable blueprint](https://ethanxli.github.io/lean-regression/blueprint.pdf)
- [Statement audit](docs/STATEMENT_AUDIT.md): every headline hypothesis classified against
  textbook formulations.
- [Rosetta table](docs/ROSETTA.md): Lean names, textbook notation, and plain English.
- [Axiom certificate](docs/AXIOMS.txt): committed output of `#print axioms` for the main results.
- [Scope and limitations](docs/SCOPE.md): exactly what is—and is not—proved.

## Main results

- `LeanRegression.frischWaughLovell`: scalar FWL over an abstract nuisance subspace.
- `LeanRegression.vectorFrischWaughLovell`: vector FWL for a finite regressor family.
- `LeanRegression.partitionedOls_regressorBlock_eq_vectorPartialRegressionCoefficient`: the
  fixed-design block-OLS theorem.
- `LeanRegression.FixedDesign.gaussMarkov_blue_centered`: expectation-unbiasedness for every
  parameter and covariance optimality in Loewner order.
- `LeanRegression.FixedDesign.aitken_gls_blue`: GLS/Aitken covariance optimality under a supplied
  whitening equivalence.
- `LeanRegression.conditionalPredictor_minimal`: conditional expectation minimizes mean squared
  prediction error.

No Gaussianity and no independence of error coordinates are assumed by Gauss–Markov.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```text
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

The checked-in `lean-toolchain` and `lake-manifest.json` pin Lean and every Lake dependency. CI
rebuilds that fixed environment from scratch. A separate weekly workflow checks the same sources
against Mathlib `master` and its matching Lean toolchain; failure there is an early compatibility
warning and does not weaken the pinned build.

## Use as a dependency

```toml
[[require]]
name = "lean_regression"
git = "https://github.com/ethanxli/lean-regression"
rev = "main"
```

Then import either `LeanRegression` or a focused module such as
`LeanRegression.FrischWaughLovell`.

## Citation and releases

Use [CITATION.cff](CITATION.cff) for citation metadata. Tagged releases are intended to be
archived through Zenodo; the release checklist requires adding the minted DOI to both
`CITATION.cff` and `.zenodo.json`. The repository deliberately has no release tag until a Zenodo
archive has been minted, so no non-archived tag is presented as citable.

## Contributing

Contributions are welcome. Please read [CONTRIBUTING.md](CONTRIBUTING.md). By contributing, you
agree that your changes are licensed under Apache-2.0.
