# rocq-domain-theory — Project Structure

A modernization of the Benton-Kennedy (2009) domain theory library for
Rocq 9.0, extended with enriched category theory and quantum CPO foundations.
Uses the Hierarchy Builder (HB) packed-class framework throughout.

---

## Directory Layout

```
rocq-domain-theory/
├── docs/
│   ├── design-decisions.md     ← architectural choices and rationale
│   ├── migration-notes.md      ← notes on porting from Coq 8.2
│   └── tutorial/               ← user-facing tutorial notebooks
│
├── src/
│   ├── structures/             ← HB mixin/structure declarations (no proofs)
│   ├── theory/                 ← lemmas, constructions, proofs
│   ├── instances/              ← concrete HB instance registrations
│   ├── lang/                   ← PCF and quantum language semantics
│   └── quantum/                ← quantum CPO structures (Phase 2)
│
├── test/                       ← sanity-check files
├── examples/                   ← worked examples
└── scripts/
    └── build.sh
```

**Build order enforced by dune:**
```
DomainTheory.Structures
  └── DomainTheory.theory
        └── DomainTheory.instances
              └── DomainTheory.lang / DomainTheory.quantum
```

---

## Phase Map

| Phase | Scope | Status |
|-------|-------|--------|
| 0 | Modernize Benton-Kennedy library (CPOs, constructions, PCF adequacy) | In progress |
| 1 | Enriched categories, locally continuous functors, D ≅ [D→D]⊥ | Structures done |
| 2 | Quantum CPO structures (stretch goal) | Not started |
| 3 | QMini-Core language prototype (stretch goal) | Not started |

---

## `src/structures/` — Structure Declarations

All files in this directory contain **only** HB mixin and structure
declarations. No proofs, no lemmas. The dune library name is
`DomainTheory.Structures`.

> **Note on `Pointed.v`:** There is no `Pointed.v`. `HasBot`, `IsPointed`,
> and `PointedCPO` live in `CPO.v`; `strict_fun` lives in `Morphisms.v`.
> See `docs/design-decisions.md § DD-001`.

---

### `Order.v` ✓ (Phase 0) — 183 lines

**Dune module:** `Order`
**Imports:** Rocq stdlib, HB only

| Name | Kind | Description |
|------|------|-------------|
| `HasLe` | HB mixin | carrier type with a `≤` relation |
| `IsPreorder` | HB mixin | reflexivity + transitivity of `≤` |
| `Preorder` | HB structure | bundled preorder |
| `IsPartialOrder` | HB mixin | antisymmetry; requires `IsPreorder` |
| `PartialOrder` | HB structure | bundled partial order |
| `chain` | Definition | ω-chain: monotone `ℕ → T` |
| `mono_fun` | Record | monotone function + proof |
| `monotone` | Definition | predicate: `f` preserves `≤` |

Reference: A&J Definition 2.1.1 (preorder), 2.1.2 (partial order).

---

### `CPO.v` ✓ (Phase 0) — 163 lines

**Dune module:** `CPO`
**Imports:** `Order`

| Name | Kind | Description |
|------|------|-------------|
| `HasSup` | HB mixin | `sup : chain T → T` function |
| `IsCPO` | HB mixin | `sup_upper` and `sup_least` axioms; requires `PartialOrder` |
| `CPO` | HB structure | bundled ω-CPO |
| `continuous` | Definition | predicate: `f` preserves chain sups |
| `HasBot` | HB mixin | distinguished bottom element `⊥` |
| `IsPointed` | HB mixin | `⊥` is least; requires `CPO` + `HasBot` |
| `PointedCPO` | HB structure | bundled pointed ω-CPO |

Reference: A&J Definition 2.1.13 (CPO built on partial order).
Benton-Kennedy §2.1 (`cpo` record).

---

### `Morphisms.v` ✓ (Phase 0) — 162 lines

**Dune module:** `Morphisms`
**Imports:** `Order`, `CPO`

| Name | Kind | Description |
|------|------|-------------|
| `cont_fun` | Record | Scott-continuous function + proofs |
| `cont_id` | Definition | identity continuous function |
| `cont_comp` | Definition | composition of continuous functions |
| `cont_id_l/r` | Lemma | `id ∘ f = f`, `f ∘ id = f` |
| `cont_comp_assoc` | Lemma | associativity of `cont_comp` |
| `strict` | Definition | predicate: `f ⊥ = ⊥` |
| `strict_fun` | Record | strict continuous function + proof |
| `strict_id` | Lemma | identity is strict |
| `strict_comp` | Lemma | composition of strict functions is strict |

Note: `cont_fun D E` is not yet an HB-registered `CPO.type`. That
registration is deferred to `instances/Function.v` once the pointwise
order is developed in `theory/FunctionSpaces.v`.

Reference: A&J §3.2.2. Benton-Kennedy §2.1 (`fconti` record).

---

### `Enriched.v` ✓ (Phase 1) — 344 lines

**Dune module:** `Enriched`
**Imports:** `Order`, `CPO`, `Morphisms`

| Name | Kind | Description |
|------|------|-------------|
| `HasHom` | HB mixin | `hom : Obj → Obj → CPO.type` |
| `HasId` | HB mixin | `id_mor : hom A A` |
| `HasComp` | HB mixin | `comp : hom B C → hom A B → hom A C` |
| `⊚` | Notation | diagrammatic composition (`f ⊚ g` = "g then f") |
| `IsCPOEnriched` | HB mixin | separate Scott-continuity of `comp` in each arg; categorical laws |
| `CPOEnrichedCat` | HB structure | bundled CPO-enriched category |
| `comp_l_cont_fun` | Definition | post-composition packaged as `cont_fun` |
| `comp_r_cont_fun` | Definition | pre-composition packaged as `cont_fun` |
| `HasEndo` | HB mixin | `F_obj : Obj → Obj`, `F_mor` action on morphisms |
| `IsLocallyContinuous` | HB mixin | A&J Def 5.2.3: `F_mor` Scott-continuous on each hom-CPO; functoriality |
| `LocallyContinuousFunctor` | HB structure | bundled locally continuous endofunctor |
| `F_mor_cont_fun` | Definition | `F_mor` packaged as `cont_fun` |
| `HasMixedEndo` | HB mixin | **data only**: `MF_obj : Obj → Obj → Obj`, `MF_mor` (contra × covariant) |

Design notes:
- Separate continuity used instead of joint continuity to avoid a
  dependency cycle with `Products.v` (see `design-decisions.md § DD-002`).
- `HasMixedEndo` records only data; axioms (`IsMixedLocallyContinuous`)
  are deferred to `theory/DomainEquations.v` (see `§ DD-005`).

References: A&J §5.2.2, Def 5.2.3, Def 5.2.5. Benton-Kennedy §4
(`BiFunctor` record). Kornell-Lindenhovius-Mislove (2024) §3.3.

---

## `src/theory/` — Proofs and Constructions

All files import from `DomainTheory.Structures`. The dune library name
is `DomainTheory.Theory`.

---

### `OrderTheory.v` ✗ (Phase 0) — *not yet written*

**Imports:** `Order`

Planned: antisymmetry consequences, the equivalence relation
`x == y ↔ x ≤ y ∧ y ≤ x`, chain monotonicity lemmas, setoid instances.

---

### `ChainTheory.v` ✗ (Phase 0) — *not yet written*

**Imports:** `Order`, `OrderTheory`

Planned: tail of a chain is a chain, constant chains, eventually-constant
chains, chain comparison lemmas.

---

### `CPOTheory.v` ✗ (Phase 0) — *not yet written*

**Imports:** `CPO`, `Morphisms`, `OrderTheory`, `ChainTheory`

Planned: sup/lub lemmas, Scott continuity properties, admissible
predicates, Scott induction principle.

Reference: A&J §2.1, §2.2. Benton-Kennedy §2.1.

---

### `FixedPoints.v` ✗ (Phase 0) — *not yet written*

**Imports:** `CPO`, `Morphisms`, `CPOTheory`

Planned: Kleene fixed-point theorem (`fix f = ⊔_n fⁿ(⊥)`),
`FIXP : (D ⇒c D) →c D`, fixed-point induction principle.

Reference: A&J §2.1.3. Benton-Kennedy §2.1 (`fixp`, `FIXP`, `fixp_ind`).

---

### `Products.v` ✗ (Phase 0) — *not yet written*

**Imports:** `CPO`, `Morphisms`, `CPOTheory`

Planned: product CPO `D × E`, projections `π₁`/`π₂`, pairing `⟨f,g⟩`,
pointwise sup. `D × E` is a `CPO`; pointed when both factors are pointed.

Reference: A&J §3.2.1. Benton-Kennedy §2.1.

---

### `Sums.v` ✗ (Phase 0) — *not yet written*

**Imports:** `CPO`, `Morphisms`, `CPOTheory`

Planned: separated sum CPO `D ⊕ E`, injections, case analysis.
Note: not strict in general (Benton-Kennedy note on `BiSum`).

---

### `FunctionSpaces.v` ✗ (Phase 0) — *not yet written*

**Imports:** `CPO`, `Morphisms`, `CPOTheory`, `Products`

Planned: function-space CPO `D ⇒ E` with pointwise order, `curry`,
`uncurry`, `ev`. Proof that `CPO` is Cartesian closed.

Unlocks: `instances/Function.v` can register `CPO.type` as a
`CPOEnrichedCat` instance once this file exists.

Reference: A&J §3.2.2. Benton-Kennedy §2.1.

---

### `Lift.v` ✗ (Phase 0) — *not yet written*

**Imports:** `CPO`, `Morphisms`, `CPOTheory`

Planned: lifting construction `D⊥`, the lift monad (`η`, `kleisli`),
`D⊥` as a `PointedCPO`.

Reference: Benton-Kennedy §2.2 (coinductive `Stream`-based constructive
lift). A&J §2.1.4.

---

### `EnrichedTheory.v` ✗ (Phase 1) — *not yet written*

**Imports:** `Enriched`, `CPOTheory`, `FunctionSpaces`

Planned: enriched natural transformations, proof of A&J Proposition 5.2.4
(locally continuous functor restricts to continuous functor on embeddings),
Yoneda in the enriched setting.

---

### `NatTrans.v` ✗ (Phase 1) — *not yet written*

**Imports:** `Enriched`, `EnrichedTheory`

Planned: enriched natural transformations as a CPO (pointwise order),
horizontal and vertical composition.

---

### `DomainEquations.v` ✗ (Phase 0/1) — *not yet written*

**Imports:** `Enriched`, `Products`, `FunctionSpaces`, `Lift`,
`EnrichedTheory`

Planned:
- `IsMixedLocallyContinuous` mixin (axioms for `HasMixedEndo`)
- Embedding-projection pairs
- Bilimit / inverse-limit construction (Scott / Freyd-Pitts method)
- Proof: bilimit is canonical solution to `X ≅ F(X)`
- Corollary: `D ≅ [D → D]⊥`

Reference: A&J §5.2–5.3. Benton-Kennedy §4. Pitts (1996).

---

## `src/instances/` — Concrete Instance Registrations

All files import from both `DomainTheory.Structures` and
`DomainTheory.Theory`. The dune library name is `DomainTheory.Instances`.

| File | Phase | Registers |
|------|-------|-----------|
| `Nat.v` | 0 | `nat` with `≤` as `CPO.type` |
| `Discrete.v` | 0 | `Discrete X` (equality order) as `CPO.type` |
| `Lift.v` | 0 | `D⊥` as `PointedCPO.type` |
| `Product.v` | 0 | `D × E` as `CPO.type`; `PointedCPO.type` when both pointed |
| `Sum.v` | 0 | `D ⊕ E` as `CPO.type` |
| `Function.v` | 0/1 | `D ⇒ E` as `CPO.type`; `CPO.type` as `CPOEnrichedCat` |
| `Quantum.v` | 2 | qCPO instances (stretch goal) |

The `Function.v` registration of `CPO.type` as `CPOEnrichedCat`:
```coq
hom D E  := fun_cpo D E     (* function-space CPO *)
id_mor   := cont_id
comp     := cont_comp
```

---

## `src/lang/` — Language Semantics

Dune library: `DomainTheory.lang`. Depends on `DomainTheory.instances`.

| File | Phase | Description |
|------|-------|-------------|
| `PCF_Syntax.v` | 1 | PCF types, terms (strongly-typed de Bruijn) |
| `PCF_Operational.v` | 1 | Big-step evaluation relation |
| `PCF_Denotational.v` | 1 | Denotational semantics |
| `PCF_Soundness.v` | 1 | `e ⇓ v → ⟦e⟧ = η(⟦v⟧)` |
| `PCF_Adequacy.v` | 1 | Computational adequacy via logical relations |
| `QMiniCore_Syntax.v` | 2/3 | Quantum lambda calculus syntax |
| `QMiniCore_Semantics.v` | 2/3 | Quantum denotational semantics |

Reference: Benton-Kennedy §3 (strongly-typed de Bruijn, `SemTy`,
`SemExp`, `relVal`/`relExp` logical relation).

---

## `src/quantum/` — Quantum CPO Structures (Phase 2, stretch)

Dune library: `DomainTheory.quantum`. Depends on `DomainTheory.instances`.

| File | Description |
|------|-------------|
| `QuantumStructure.v` | Quantum sets, quantum posets |
| `qCPO.v` | qCPO definition |
| `QuantumMorphisms.v` | Scott-continuous quantum morphisms |
| `qCPOProperties.v` | qCPO is enriched over CPO (KLM §3.3) |
| `QuantumEnrichment.v` | Quantum enrichment structure |

Reference: Kornell-Lindenhovius-Mislove (2021, 2024).

---

## Key Dependency Graph

```
Order.v
  └── CPO.v
        ├── Morphisms.v
        │     └── Enriched.v
        │
        └── [theory/]
              ├── OrderTheory.v
              ├── ChainTheory.v      ← OrderTheory
              ├── CPOTheory.v        ← ChainTheory, Morphisms
              ├── FixedPoints.v      ← CPOTheory
              ├── Products.v         ← CPOTheory
              ├── Sums.v             ← CPOTheory
              ├── FunctionSpaces.v   ← Products
              ├── Lift.v             ← CPOTheory
              ├── EnrichedTheory.v   ← Enriched, FunctionSpaces
              ├── NatTrans.v         ← EnrichedTheory
              └── DomainEquations.v  ← Enriched, Products,
                                        FunctionSpaces, Lift,
                                        EnrichedTheory
```

---

## Line Count (completed files)

| File | Lines | Status |
|------|-------|--------|
| `src/structures/Order.v` | 183 | ✓ Done |
| `src/structures/CPO.v` | 163 | ✓ Done |
| `src/structures/Morphisms.v` | 162 | ✓ Done |
| `src/structures/Enriched.v` | 344 | ✓ Done |
| **Structures subtotal** | **852** | |
| `src/theory/` (all files) | — | ✗ Not started |
| `src/instances/` (all files) | — | ✗ Not started |
| `src/lang/` (all files) | — | ✗ Not started |

Thesis target for Phase 0+1 total: ~2,000–2,500 lines of specification.