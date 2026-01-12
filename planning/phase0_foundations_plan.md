# Phase0 Foundations Implementation Plan

**Created:** 2026-01-09
**Owner:** GitHub Copilot

## Goal 🎯
Finish and harden the `src/phase0_foundations` module set so that:
- all proofs are complete (no remaining `admit`),
- definitions/instances integrate cleanly with Hierarchy-Builder (HB) mixins, and
- there are unit tests that exercise core lemmas (CPO lubs, products, continuity, fixed point).

## Acceptance criteria ✅
- `dune build` succeeds with no unresolved admits in `phase0_foundations`.
- `dune runtest` covers added tests and they pass.
- A PR `feature/foundations` is opened with focused changes and tests.

## High-level tasks (priority order) 🔧
1. Inventory files & find unfinished proofs/comments (search for `admit`, `TODO`, `Content to be added`).
2. Replace `admit` with constructive proofs or detailed `Admitted` justifications where temporary (short-lived).
3. Ensure HB mixins are consistent: verify `From HB Require Import structures.` is used where needed and not missing.
4. Add unit tests for:
   - CPO lub correctness (upper bound and least property)
   - Product cpo lubs
   - Continuous functions preserving lubs
   - Fixed point induction on pointed CPOs
5. Run full build & tests, fix any type/universe issues.
6. Split large changes into incremental commits and open `feature/foundations` PR; include tests that initially fail then get fixed.

## File-level plan
- `Order.v` — review final form; ensure mixins/notations are correct and consistent with HB usage.
- `nOrder.v` — ensure its notations/imports compile with HB.
- `CPO.v` — replace `admit` obligations in `fun_cpo` and `prod_cpo` with complete proofs.
- `Continuous.v`, `FixedPoints.v`, `Products.v` — add tests and check proofs.

## Tests to add
- `test/foundations_lub.v` — tests for `lub_of_chain` upper/least.
- `test/foundations_products.v` — tests for product cpo lubs.
- `test/foundations_fixedpoint.v` — test `fixp` and `fixp_ind`.

## Branching & PR
- Branch name: `feature/foundations`
- Small commits with clear messages; include at least one test per commit that fails before the fix to follow test-driven workflow.

## Time estimates
- Inventory & test scaffolding: 1–2 days
- Replacing admits & completing proofs: 2–5 days (depends on complexity)
- Tests, CI updates, PR: 1–2 days

---

If this plan looks good, I'll create branch `feature/foundations` and start with the inventory plus the `fun_cpo` / `prod_cpo` proofs in `CPO.v` (those currently contain `admit`).