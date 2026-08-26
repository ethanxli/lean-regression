# Release checklist

1. Confirm the pinned CI, blueprint build, API documentation, and Mathlib-master compatibility
   check are green.
2. Regenerate and commit `docs/AXIOMS.txt`; inspect it for `sorryAx` or any axiom outside the
   documented Lean/Mathlib baseline.
3. Update the version in `lakefile.toml` and `CITATION.cff`.
4. Enable the repository in the maintainer's Zenodo GitHub integration.
5. Create the GitHub release and tag. Zenodo will archive that release and mint a version DOI.
6. Add the version DOI to `CITATION.cff` (`doi:`) and `.zenodo.json` (`doi`), then publish a
   metadata-only patch if required. Keep Zenodo's concept DOI in the README for release-agnostic
   citation and the version DOI in each release record.

Minting a DOI requires the repository owner's authenticated Zenodo account and therefore cannot
be performed by unauthenticated CI.
