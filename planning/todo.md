# Proposal Checklist (grounded in .v3 Thesis Proposal)

This is a direct, implementation-oriented checklist derived from the proposal’s:
- **Core Objectives** (Phase 0 + Phase 1)
- **Monthly milestones**
- **Success criteria** (TI/TII/TIII)

Notes:
- Current builds are on Rocq 9.0.0; proposal text mentions Rocq 8.20. If strict 8.20 compatibility is required, add CI or a dedicated opam switch to verify.
- The main technical gap today is that `lub_of_chain`/`continuous` range over arbitrary `nat -> D`, not **monotone ω-chains**.

## TI: Minimum viable thesis (proposal “Success Criteria”)

### TI.1 Modernized Benton–Kennedy library runs
- [ ] Phase 0 foundations compile cleanly as a library
	- Files: `src/phase0_foundations/*`
- [ ] Replace “ω-sequence lubs” with **ω-chain** lubs
	- Add `chain` definition (monotone `nat -> D`) in: `src/phase0_foundations/Order.v` (or a new `Chains.v`)
	- Update CPO interface: `src/phase0_foundations/CPO.v`
	- Update continuity definition: `src/phase0_foundations/Continuous.v`
	- Update constructions accordingly: `src/phase0_foundations/Products.v`, `src/phase0_foundations/FunctionSpaces.v`
- [ ] Implement (or remove) Phase 0 placeholders that are referenced in the proposal’s Phase 0 scope
	- Predomains: `src/phase0_foundations/Predomains.v`
	- Lift monad: `src/phase0_foundations/Lift.v`
	- Sums: `src/phase0_foundations/Sums.v`

### TI.2 Basic enriched category formalization (Phase 1)
- [ ] Define ω-chain enriched categories (Enriched_Cat)
	- Files: `src/phase1_enriched/EnrichedCategory.v`, `src/phase1_enriched/CPOEnriched.v`
- [ ] Define locally-continuous functors
	- File: `src/phase1_enriched/LocallyContinuous.v`
- [ ] Define enriched natural transformations
	- File: `src/phase1_enriched/EnrichedNatTrans.v`

### TI.3 At least one adequacy proof (PCF)
- [ ] Implement PCF syntax and operational semantics
	- Files: `src/phase1_validation/PCF_Syntax.v`, `src/phase1_validation/PCF_Operational.v`
- [ ] Implement denotational semantics using the (enriched) domain library
	- File: `src/phase1_validation/PCF_Denotational.v`
- [ ] Prove soundness + adequacy
	- Files: `src/phase1_validation/PCF_Soundness.v`, `src/phase1_validation/PCF_Adequacy.v`

### TI.4 Written thesis explaining contributions
- [ ] Fill thesis chapters with actual content (not placeholders)
	- Files: `docs/thesis/introduction.md`, `docs/thesis/background.md`, `docs/thesis/methods.md`, `docs/thesis/results.md`, `docs/thesis/discussion.md`, `docs/thesis/conclusion.md`

## Phase 0 (proposal Weeks 1–8): Domain theory modernization

### Core definitions
- [ ] Preorders + monotone functions
	- File: `src/phase0_foundations/Order.v`
- [ ] CPOs (ω-chain lubs) + pointed cpos
	- File: `src/phase0_foundations/CPO.v`
- [ ] Continuous maps / cont_fun
	- File: `src/phase0_foundations/Continuous.v`

### Basic constructions
- [ ] Products
	- File: `src/phase0_foundations/Products.v`
- [ ] Function spaces (exponentials)
	- File: `src/phase0_foundations/FunctionSpaces.v`
- [ ] Sums (coproducts)
	- File: `src/phase0_foundations/Sums.v`
- [ ] Lift monad / flat domains
	- File: `src/phase0_foundations/Lift.v`

### Recursive domain equations (proposal Week 7–8)
- [ ] InverseLimit module (core deliverable of Phase 0)
	- Files: `src/phase0_inverse_limit/InverseLimit.v`, `src/phase0_inverse_limit/RecursiveDomains.v`, `src/phase0_foundations/RecursiveDomains.v`

### Validation
- [ ] `dune build` and `dune runtest` green
	- Tests live under: `test/`
- [ ] Add at least one “basic example” file that uses the library end-to-end
	- Candidate: `examples/examples.v`

## Phase 1 (proposal Weeks 9–18): Enriched categories

### Define basic enriched category structures
- [ ] ω-chain enriched categories
	- File: `src/phase1_enriched/EnrichedCategory.v`
- [ ] Locally-continuous functors
	- File: `src/phase1_enriched/LocallyContinuous.v`
- [ ] Enriched natural transformations
	- File: `src/phase1_enriched/EnrichedNatTrans.v`

### Prove CPO is enriched
- [ ] Hom-objects are CPOs
- [ ] Composition is continuous
- [ ] Enriched category laws
	- File: `src/phase1_enriched/CPOEnriched.v`

### Lift inverse-limit theorem to enriched setting + derive key equation D
- [ ] Enriched inverse-limit theorem
	- File: `src/phase1_enriched/EnrichedInverseLimit.v`
- [ ] Derive domain equation D
	- File: `src/phase1_enriched/RecursiveEquations.v`

### Validation
- [ ] Adequacy proof uses the enriched framework (not just “plain” CPO)
	- File: `src/phase1_validation/PCF_Adequacy.v`

## Stretch goals (proposal Phases 2–3)

### Phase 2: qCPO structures (optional)
- [ ] Define qCPO category + morphisms + basic axioms
	- Files: `src/phase2_quantum/qCPO.v`, `src/phase2_quantum/QuantumMorphisms.v`, `src/phase2_quantum/QuantumStructure.v`

### Phase 3: QMini-Core prototype (optional)
- [ ] Syntax + denotational semantics + examples
	- Files: `src/phase3_prototype/QMiniCore_Syntax.v`, `src/phase3_prototype/QMiniCore_Semantics.v`

