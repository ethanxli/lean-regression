# Contributing

Thank you for improving Lean Regression.

1. Open an issue for a theorem whose mathematical statement or scope is not obvious.
2. Keep public declarations in the `LeanRegression` namespace and add focused module imports.
3. Document the textbook statement being encoded and update `docs/STATEMENT_AUDIT.md` whenever a
   headline theorem's signature changes.
4. Run `lake build`, `lake env lean AxiomAudit.lean`, and the relevant blueprint declaration check.
5. Do not introduce `sorry`, `admit`, or new axioms. If classical reasoning is unavoidable, make
   it visible in `docs/AXIOMS.txt`.
6. Keep pull requests small enough that the proof idea and signature can be reviewed together.

All contributions are licensed under Apache-2.0.
