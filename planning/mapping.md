# Mapping: Thesis Deliverables → Repository

**Created:** 2026-01-09
**Author:** GitHub Copilot

## Summary
This document maps the thesis deliverables (from your proposal) to the repository modules and files, notes missing/partial pieces, and proposes the next tasks and priorities. I will open a draft branch `mapping/proposal-tasks` with this file for your review.

---

## Deliverables and mapping
- Formalize basic order/CPO theory (deliverable: foundations)
  - Files: `src/phase0_foundations/Order.v`, `src/phase0_foundations/nOrder.v`, `src/phase0_foundations/tmixins.v`, `src/phase0_foundations/Continuous.v`, `src/phase0_foundations/CPO.v`, `src/phase0_foundations/Products.v` (and related modules)
  - Status: Mostly present. Some minor import/structure fixes applied (e.g., `nOrder.v`).

- Hierarchy-Builder integration (deliverable: structuring + mixins)
  - Files: `src/phase0_hierarchybuilder/Hierarchies.v`, `src/phase0_hierarchybuilder/Instances.v`
  - Status: Present; needs finishing mixins and instances for CPOs, products, pointed structures.

- Inverse limit constructions & recursive domains
  - Files: `src/phase0_inverse_limit/InverseLimit.v`, `src/phase0_inverse_limit/BiFunctor.v`, `src/phase0_inverse_limit/EmbeddingProjection.v`
  - Status: Present; check proofs for completeness and test coverage.

- Enriched categories and continuity
  - Files: `src/phase1_enriched/EnrichedCategory.v`, `src/phase1_enriched/CPOEnriched.v`, `src/phase1_enriched/EnrichedInverseLimit.v`
  - Status: Present; validate type universes and interactions with `SProp` and `primitive projections`.

- Validation (PCF adequacy, operational/denotational semantics)
  - Files: `src/phase1_validation/PCF_Adequacy.v`, `src/phase1_validation/PCF_Denotational.v`, `src/phase1_validation/PCF_Operational.v`, `src/phase1_validation/PCF_Soundness.v`, `src/phase1_validation/PCF_Syntax.v`
  - Status: Core proofs present; add more examples and regression tests.

- Quantum enrichment and quantum CPOs
  - Files: `src/phase2_quantum/qCPO.v`, `src/phase2_quantum/qCPOProperties.v`, `src/phase2_quantum/QuantumEnrichment.v`, `src/phase2_quantum/QuantumStructure.v`
  - Status: In place; review correctness of quantum enrichment lemmas and add unit proofs for subtle steps.

- Prototype semantics & examples (QMiniCore)
  - Files: `src/phase3_prototype/QMiniCore_Syntax.v`, `src/phase3_prototype/QMiniCore_Semantics.v`, `src/phase3_prototype/examples/*`
  - Status: Prototype present; expand examples and integrate with CI tests.

- Tests & example suite
  - Files: `test/test_suite.v`, `examples/examples.v`
  - Status: Minimal; increase coverage for critical modules (validation, inverse limits, qCPO properties).

- Documentation & thesis write-up
  - Files: `docs/thesis/*`, `README.md`, `docs/tutorial/*`
  - Status: Thesis material present; we should add more implementation details and reproducibility notes (opam pin, lock files).

---

## Missing / Partial Items
- Some HB notation imports were inconsistent (e.g., `nOrder.v` had a missing `notation` import — fixed by commenting it out). Verify all places using HB notations work as intended.
- Tests are sparse for phase2 (quantum) and phase3 (prototype). Add focused unit tests.
- No CI workflow currently (add GitHub Actions to run `dune build` / `dune runtest` on push with matrix for OCaml/Coq versions).
- Consider adding an `opam.lock` or `coq_modules` file to guarantee reproducible builds for submission.

---

## Proposed next tasks (priority order)
1. Add targeted tests for `phase1_validation` and `phase2_quantum` modules (high priority).
2. Finish HB mixins/instances for CPOs and products in `phase0_hierarchybuilder`.
3. Expand prototype examples and tie to `test_suite.v` (high priority).
4. Add GitHub Actions CI to run `dune build` and `dune runtest` on PRs and pushes.
5. Add a reproducibility manifest (`opam.lock`/`opam` pin instructions) and `docs/BUILD.md` describing dev environment (opam 2.1.5, Rocq 9.0.0).

---

## Suggested branch & PR strategy
- Branch naming: `feature/<area>-<short-desc>` (e.g., `feature/tests-quantum`).
- Small focused PRs for each task; include failing tests first when introducing a fix.

---

## Acceptance criteria for main deliverables
- All core proofs typecheck and are covered by tests.
- CI runs on every PR and build is reproducible with documented steps.
- Thesis sections updated to reference the implementation and include example outputs.