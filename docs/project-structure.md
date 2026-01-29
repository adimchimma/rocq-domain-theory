# Project Structure & Architecture

## Overview

This thesis project formalizes **modernized domain theory** in Rocq 9.0.0, with applications to denotational semantics and quantum programming languages. The codebase is organized into **three major phases**, each building on the previous:

- **Phase 0 (Weeks 1–8)**: Modernized domain theory foundations
- **Phase 1 (Weeks 9–18)**: Enriched category formalization  
- **Phase 2–3**: Quantum extensions & prototype (optional)

---

## Directory Layout

```
rocq-domain-theory/
├── src/
│   ├── phase0_foundations/        # Core order & CPO theory
│   ├── phase0_hierarchybuilder/   # Automatic hierarchy & instance generation
│   ├── phase0_inverse_limit/      # Recursive domain equations
│   ├── phase1_enriched/           # Enriched category structures
│   ├── phase1_validation/         # PCF adequacy proof (Phase 1)
│   ├── phase2_quantum/            # Quantum extensions (optional)
│   └── phase3_prototype/          # Prototype interpreter (optional)
│
├── docs/                          # Thesis & technical documentation
│   ├── thesis/                    # Thesis chapters
│   ├── tutorial/                  # Usage examples
│   └── design-decisions.md        # Architectural notes
│
├── test/                          # Test suite
├── planning/                      # Project planning docs
├── examples/                      # Example programs
└── dune, dune-project             # Build configuration
```

---

## Phase 0: Modernized Domain Theory Foundations

### Purpose
Establish a modern, provably correct library for order-theoretic domain theory, replacing ad-hoc definitions with proper mathematical structures.

### Key Modules

#### **Order.v** — Preorders & ω-Chains
- `preorder`: Reflexive, transitive relations
- `chain`: **Monotone ω-sequences** (`nat → D` with `m ≤ n → f(m) ⊑ f(n)`)
- `mono_fun`: Monotone functions
- **Helper operations**: `chain_at`, `map_chain`, `const_chain`, `chain_succ_le`

**Status**: ✅ Complete with chain infrastructure integrated

#### **CPO.v** — Complete Partial Orders
- `cpo`: Record with:
  - Underlying `preorder`
  - `lub_of_chain`: Compute least upper bound of ω-chains
  - `lub_upper` & `lub_least`: Completeness axioms
- `Pointed`: Cpos with a least element (for fixpoint computation)
- `Fixpoints`: Iterate `F n` from bottom → chain → least fixed point via `fixp F`

**Status**: ✅ Refactored to use `chain` instead of arbitrary `nat → D`

#### **Continuous.v** — Continuity
- `continuous`: Function preserves lubs of chains
  - Requires: monotone function `f : mono_fun D E`
  - Ensures: `f(⊔c) = ⊔(map f c)` for all chains `c`
- `cont_fun`: Continuous function wrapper

**Status**: ✅ Updated to quantify continuity over chains

#### **Products.v** — Cartesian Products
- `prod_cpo`: Product `A × B` is a CPO with:
  - Pointwise order: `(a₁, b₁) ⊑ (a₂, b₂)` iff `a₁ ⊑ a₂` and `b₁ ⊑ b₂`
  - Pointwise lubs: `⊔c = (⊔(π₁ c), ⊔(π₂ c))`

**Status**: ✅ Compiled with chain-aware lub definitions

#### **FunctionSpaces.v** — Exponentials
- `fun_cpo`: Function space `[D ⇒ E]` as a CPO of continuous functions
  - Pointwise order on `cont_fun`
  - Pointwise lubs (axiomatized for now)

**Status**: ⚠️ Struct complete, lub implementation axiomatized

#### **Discrete.v** — Trivial CPOs
- `unit_cpo`: Unit type with discrete order

**Status**: ✅ Compiles

#### **FixedPoints.v** — Reexports
- Module re-export of fixpoint theory from CPO.v

**Status**: ✅ Compiles

#### **Predomains.v, Lift.v, Sums.v, RecursiveDomains.v**
- **Status**: ⚠️ Placeholder/stub files; need implementation per proposal

#### **Pointed.v**
- **Status**: ⚠️ Duplicate of Pointed class in CPO.v; consolidation pending

---

### Phase 0 Achievements

✅ **Modernized Library**: Replaced ad-hoc definitions with proper mathematical structures (Rocq 9.0.0, dune 3.20.2)

✅ **ω-Chain Infrastructure**: Monotone sequences `chain` replace arbitrary `nat → D` throughout:
  - Order.v: chain definition + operations  
  - CPO.v: `lub_of_chain : chain cpo_pre → carrier`
  - Continuous.v: continuity over chains
  - Products.v & FunctionSpaces.v: updated signatures

✅ **Build Clean**: `dune build && dune runtest` passes (Exit Code 0)

---

## Phase 0.5: Hierarchy Builder (Optional)

### Purpose
Automatically generate instances of algebraic hierarchies (rings, fields, vector spaces) using Rocq's hierarchy builder.

### Location
`src/phase0_hierarchybuilder/`

**Status**: ⚠️ Defined but minimal usage in Phase 0; intended for Phase 1+

---

## Phase 0.5b: Inverse Limits (Core Phase 0 Deliverable)

### Purpose
Formalize recursive domain equations via inverse limits. Enables solving domains recursively: `D ≅ [[D ⇒ D]]` (reflexive domains).

### Key Modules

#### **InverseLimit.v** — Categorical framework
- Embedding-projection pairs
- Inverse limit construction
- Convergence & completeness proofs

#### **RecursiveDomains.v** — Application to domains
- Solve `D ≅ F(D)` for a continuous functor `F`
- Derive reflexive domains

**Status**: ⚠️ Currently minimal/stub; proposal requires this as a **core Phase 0 deliverable**

---

## Phase 1: Enriched Categories

### Purpose
Lift domain theory to the **enriched setting**: categories enriched over **ω-cpo ordered morphisms**. This enables:
- Hom-objects are CPOs (not just sets)
- Natural transformations are continuous
- Recursive equations solved in enriched framework

### Key Modules

#### **EnrichedCategory.v** — Basic structures
- Enriched category over CPO base
- Enriched functors
- Enriched natural transformations

**Status**: ⚠️ Defined; need full proofs

#### **LocallyContinuous.v** — Morphism constraints
- Locally-continuous functors: natural transformations are continuous

**Status**: ⚠️ Stub

#### **EnrichedNatTrans.v** — Enriched NTs
- Natural transformations in enriched setting
- Vertical & horizontal composition

**Status**: ⚠️ Stub

#### **CPOEnriched.v** — CPO is enriched
- Prove CPO category is enriched over itself
- Hom-objects are CPOs
- Composition is continuous

**Status**: ⚠️ Stub

#### **EnrichedInverseLimit.v** — Enriched inverse limits
- Generalize inverse limits to enriched setting
- Solve enriched recursive equations

**Status**: ⚠️ Stub

#### **RecursiveEquations.v** — Domain equations
- Derive the main domain equation `D` from thesis proposal
- Solution via enriched inverse limit

**Status**: ⚠️ Stub

---

## Phase 1: Validation (PCF Adequacy)

### Purpose
Prove soundness & adequacy of denotational semantics for **PCF** (Programming Computable Functions), a core lambda calculus. This validates the entire domain theory framework.

### Key Modules

#### **PCF_Syntax.v** — Language definition
- Types: `nat`, `bool`, function types
- Terms: variables, constants, lambda, application, conditionals, recursion

**Status**: ⚠️ Stub

#### **PCF_Operational.v** — Step semantics
- Big-step or small-step evaluation
- Termination & divergence

**Status**: ⚠️ Stub

#### **PCF_Denotational.v** — Semantic domain
- Denotation `⟦τ⟧` for types (elements of CPO)
- Denotation `⟦M⟧` for terms (continuous functions)
- Lookup function for variables

**Status**: ⚠️ Stub

#### **PCF_Soundness.v** — Denotational soundness
- `M ⟹ v` (operational) → `⟦M⟧ ⊒ ⟦v⟧` (denotational)

**Status**: ⚠️ Stub

#### **PCF_Adequacy.v** — Full adequacy
- If `⟦M⟧ ≠ ⊥`, then `M` terminates (operationally)
- Converse: if `M` terminates to `v`, then `⟦M⟧ = ⟦v⟧`
- Validates the semantic foundation

**Status**: ⚠️ Stub (critical for thesis success criteria TI.3)

---

## Phase 2: Quantum Extensions (Optional)

### Purpose
Extend domain theory to handle quantum computation. Define quantum CPOs & continuity.

### Modules
- `qCPO.v`: Quantum CPO definition
- `QuantumStructure.v`: Quantum operators
- `QuantumMorphisms.v`: Quantum-continuous functions
- `QuantumEnrichment.v`: Enriched quantum structures

**Status**: ⚠️ Experimental; not required for thesis

---

## Phase 3: Prototype Interpreter (Optional)

### Purpose
Executable interpreter for the core language (PCF + quantum extensions).

**Status**: ⚠️ Minimal; defer unless thesis allows

---

## Test Suite

### Location
`test/`

### Key Tests
- `test_suite.v`: Main test file
- `foundations_*.v` (4 files): Unit tests for CPO, products, fixpoints, function spaces

**Status**: ✅ Basic tests pass; expand as Phase 1 work progresses

---

## Documentation

### Location
`docs/`

#### Thesis Chapters
- `thesis/introduction.md` — Problem statement
- `thesis/background.md` — Domain theory & enriched categories
- `thesis/methods.md` — Formalization approach
- `thesis/results.md` — Main theorems
- `thesis/discussion.md` — Implications & open problems
- `thesis/conclusion.md` — Summary
- `thesis/references.bib` — Bibliography

**Status**: ⚠️ Mostly stubs; need content from Phase 0–1 work

#### Supporting Docs
- `design-decisions.md` — Architectural rationale
- `migration-notes.md` — Rocq 8 → 9 upgrade notes
- `abstract.md` — Thesis abstract

#### Tutorials
- `tutorial/`: Usage examples (TBD)

---

## Planning & Tracking

### Location
`planning/`

#### Key Files
- **`todo.md`**: Proposal-aligned checklist with TI/TII/TIII criteria
- **`milestones.md`**: Month-by-month delivery schedule
- **`timeline.md`**: Calendar & deadlines
- **`ristk_mitigation.md`**: Risk assessment & mitigations

**Status**: ✅ Updated with Phase 0 chain progress

---

## Build System

### Configuration
- **Build tool**: Dune 3.20.2
- **Coq version**: Rocq 9.0.0 (proposal allows 8.20+)
- **Opam**: 2.1.5

### Key Build Files
- `dune-project`: Project metadata (Coq 0.10 language version)
- `src/dune`: Root library configuration
- `src/phase*/dune`: Per-phase stanzas with `-R` flags and `coqdep_flags`
- `test/dune`: Test runner configuration
- `_CoqProject`: Editor support (VsRocq) loadpaths

### Build Commands
```bash
# Full build
dune build

# Run tests
dune runtest

# Clean & rebuild
dune clean && dune build

# Interactive Rocq (if installed)
rocqide src/phase0_foundations/Order.v
```

**Status**: ✅ Clean build (Exit Code 0)

---

## Dependencies

### External Libraries
- **Rocq standard library**: `Setoid`, `Morphisms`, `RelationClasses`
- **Rocq-specific**: Hierarchy Builder (optional, for instance generation)

### Internal Dependencies

```
Order.v
  ↓
CPO.v ← Continuous.v
  ↓       ↓
Products.v, FunctionSpaces.v
  ↓
FixedPoints.v
  ↓
Discrete.v, Pointed.v
  ↓
(Phase 0.5b) InverseLimit.v, RecursiveDomains.v
  ↓
(Phase 1) EnrichedCategory.v, EnrichedInverseLimit.v
  ↓
(Phase 1) PCF_Syntax.v → PCF_Operational.v
  ↓          ↓
  ←─ PCF_Denotational.v ← PCF_Soundness.v
                  ↓
              PCF_Adequacy.v
```

---

## Success Criteria (from Proposal)

### TI: Minimum Viable Thesis
- [ ] Phase 0 foundations compile with ω-chains ✅ (mostly done)
- [ ] Basic enriched category definitions ⚠️ (TBD)
- [ ] PCF adequacy proof ⚠️ (TBD)
- [ ] Written thesis chapters ⚠️ (TBD)

### TII: Complete Core Thesis
- [ ] All Phase 0 modules finished (Predomains, Lift, Sums, etc.)
- [ ] Phase 1 enriched categories & theorems
- [ ] PCF adequacy fully proven
- [ ] Thesis drafted & coherent

### TIII: Extended Contributions
- [ ] Hierarchybuilder integration
- [ ] Quantum extensions (Phase 2)
- [ ] Recursive domain equations in enriched setting

---

## Development Workflow

### Local Setup
1. Install Rocq 9.0.0 via opam
2. Clone repository
3. `cd rocq-domain-theory && dune build`
4. For VS Code: Install VsRocq, run "Rocq: Reset"

### Making Changes
1. Edit `.v` file (e.g., `src/phase0_foundations/Order.v`)
2. Run `dune build` to check
3. Run `dune runtest` to validate
4. Update planning docs (`planning/todo.md`) if scope changes

### Common Tasks
- **Add new theorem**: Edit appropriate `.v` file, add proof, test with `dune build`
- **Add new module**: Create `src/phaseX/ModuleName.v`, add to `dune` stanza, import in dependent modules
- **Fix broken build**: Check error output, look at dependency chain, update imports/signatures
- **Update documentation**: Edit `.md` files in `docs/`, rebuild with Markdown processor if needed

---

## Key Architectural Decisions

1. **ω-Chains over arbitrary sequences**: Monotone chains (`m ≤ n → f(m) ⊑ f(n)`) are more natural for domain theory and avoid pitfalls of arbitrary sequences.

2. **Rocq 9.0.0**: Modernized proof assistant with better universe polymorphism and SProp support (proposal approved 8.20+).

3. **Dune over _CoqProject**: Dune handles compilation; `_CoqProject` is editor-only (VsRocq loadpaths).

4. **Axioms vs. Admits**: Critical proofs are proven; library-building operations (like function space lubs) are axiomatized to enable Phase 1 work to proceed.

5. **Module organization**: Clear phase boundaries allow parallel work and incremental validation.

---

## Next Steps (Priority Order)

1. **Phase 0 completion**:
   - Implement `Predomains.v`, `Lift.v`, `Sums.v` stubs
   - Flesh out `InverseLimit.v` & `RecursiveDomains.v`

2. **Phase 1 groundwork**:
   - Define enriched category structure in `EnrichedCategory.v`
   - Prove CPO is enriched in `CPOEnriched.v`

3. **PCF adequacy**:
   - Implement syntax, operational, denotational semantics
   - Prove soundness & adequacy

4. **Thesis writing**:
   - Draft chapters using Phase 0–1 results

5. **Optional (if time)**: Quantum extensions, prototype interpreter

---

## Summary Table

| Phase | Module | Status | Notes |
|-------|--------|--------|-------|
| 0 | Order.v | ✅ | Chain infrastructure complete |
| 0 | CPO.v | ✅ | Using chains |
| 0 | Continuous.v | ✅ | Chain-aware continuity |
| 0 | Products.v | ✅ | Compiled |
| 0 | FunctionSpaces.v | ⚠️ | Axiomatized lubs |
| 0 | Predomains.v, Lift.v, Sums.v | ❌ | Need implementation |
| 0.5b | InverseLimit.v | ⚠️ | Minimal; needs work |
| 1 | EnrichedCategory.v | ⚠️ | Stub |
| 1 | CPOEnriched.v | ⚠️ | Stub |
| 1 | PCF_Syntax.v–Adequacy.v | ⚠️ | Critical; all stubs |
| Docs | Thesis chapters | ⚠️ | Need content |
| 2–3 | Quantum, Prototype | ⚠️ | Optional |

---

*Last updated: January 2026 (after Phase 0 chain integration)*
