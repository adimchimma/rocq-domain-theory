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
│   ├── migration-notes.md      ← notes on porting from Coq 8.x
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
DomainTheory.structures
  └── DomainTheory.theory
        └── DomainTheory.instances
              └── DomainTheory.lang / DomainTheory.quantum
```

---

## Phase Map

| Phase | Scope | Status |
|-------|-------|--------|
| 0 | Modernize Benton-Kennedy library (CPOs, constructions, fixed points, lift) | **Structures done; theory layer complete** |
| 1 | Enriched categories, locally continuous functors, D ≅ [D→D]⊥ | Structures done; theory not started |
| 2 | Quantum CPO structures (stretch goal) | Not started |
| 3 | QMini-Core language prototype (stretch goal) | Not started |

---

## `src/structures/` — Structure Declarations

All files contain **only** HB mixin and structure declarations — no
proofs, no lemmas. Dune library: `DomainTheory.structures`.

> **Note on `Pointed.v`:** There is no `Pointed.v`. `HasBot`, `IsPointed`,
> and `PointedCPO` live in `CPO.v`; `strict_fun` lives in `Morphisms.v`.
> See `docs/design-decisions.md § DD-001`.

---

### `Order.v` ✓ (Phase 0) — 195 lines

**Imports:** Rocq stdlib, HB only

| Name | Kind | Description |
|------|------|-------------|
| `HasLe` | HB mixin | carrier type with a `≤` relation |
| `IsPreorder` | HB mixin | reflexivity + transitivity of `≤` |
| `Preorder` | HB structure | bundled preorder |
| `IsPartialOrder` | HB mixin | antisymmetry; requires `IsPreorder` |
| `PartialOrder` | HB structure | bundled partial order |
| `chain` | Record | ω-chain: monotone `ℕ → T`; `c.[n]` notation |
| `mono_fun` | Record | monotone function + proof |
| `monotone` | Definition | predicate: `f` preserves `≤` |
| `map_chain` | Definition | apply a `mono_fun` to a chain pointwise |
| `const_chain`, `tail_chain` | Definitions | constant and tail chains |
| `pequiv` (`≈`) | Definition | preorder equivalence `x ⊑ y ∧ y ⊑ x` |

Reference: A&J Definition 2.1.1 (preorder), 2.1.2 (partial order).

---

### `CPO.v` ✓ (Phase 0) — 187 lines

**Imports:** `Order`

| Name | Kind | Description |
|------|------|-------------|
| `HasSup` | HB mixin | `sup : chain T → T` function |
| `IsCPO` | HB mixin | `sup_upper` and `sup_least` axioms; requires `PartialOrder` |
| `CPO` | HB structure | bundled ω-CPO |
| `continuous` | Definition | predicate: `f` preserves chain sups |
| `HasBottom` | HB mixin | distinguished bottom element `⊥` |
| `IsPointed` | HB mixin | `⊥` is least; requires `CPO & HasBottom` |
| `PointedCPO` | HB structure | bundled pointed ω-CPO |

**Instance ordering constraint:** `IsPointed` has `of CPO T & HasBottom T`
in its HB mixin declaration, so `HasBottom` and `IsPointed` instances
must always be registered *after* the `IsCPO` instance for a given type.
Violating this order causes a silent HB elaboration failure. See
`design-decisions.md § DD-008` and the `Lift.v` entry in
`migration-notes.md`.

Reference: A&J Definition 2.1.13. Benton-Kennedy §2.1.

---

### `Morphisms.v` ✓ (Phase 0) — 203 lines

**Imports:** `Order`, `CPO`

| Name | Kind | Description |
|------|------|-------------|
| `cont_fun` | Record | Scott-continuous function: `cf_mono` + `cf_cont` |
| `cont_id` | Definition | identity continuous function |
| `cont_comp` | Definition | composition of continuous functions |
| `cont_fun_ext` | Lemma | extensionality: equal on all inputs → equal as `cont_fun` |
| `cont_id_l/r` | Lemmas | `id ∘ f = f`, `f ∘ id = f` |
| `cont_comp_assoc` | Lemma | associativity of `cont_comp` |
| `strict` | Definition | predicate: `f ⊥ = ⊥` |
| `strict_fun` | Record | strict continuous function + proof |
| `strict_id`, `strict_comp` | Lemmas | identity is strict; composition of strict functions is strict |

Reference: A&J §3.2.2. Benton-Kennedy §2.1 (`fconti` record).

---

### `Enriched.v` ✓ (Phase 1) — 388 lines

**Imports:** `Order`, `CPO`, `Morphisms`

| Name | Kind | Description |
|------|------|-------------|
| `HasHom` | HB mixin | `hom : Obj → Obj → CPO.type` |
| `HasId` | HB mixin | `id_mor : hom A A` |
| `HasComp` | HB mixin | `comp : hom B C → hom A B → hom A C` |
| `⊚` | Notation | diagrammatic composition |
| `IsCPOEnriched` | HB mixin | separate Scott-continuity of `comp`; categorical laws |
| `CPOEnrichedCat` | HB structure | bundled CPO-enriched category |
| `comp_l_cont_fun`, `comp_r_cont_fun` | Definitions | compositions packaged as `cont_fun` |
| `HasEndo` | HB mixin | `F_obj : Obj → Obj`, `F_mor` action on morphisms |
| `IsLocallyContinuous` | HB mixin | A&J Def 5.2.3: `F_mor` Scott-continuous on each hom-CPO; functoriality |
| `LocallyContinuousFunctor` | HB structure | bundled locally continuous endofunctor |
| `HasMixedEndo` | HB mixin | **data only**: `MF_obj`, `MF_mor` (contra × covariant) |

Design notes: Separate continuity used instead of joint (DD-002);
`HasMixedEndo` records only data (DD-005).

References: A&J §5.2.2, Def 5.2.3, Def 5.2.5. Benton-Kennedy §4.
Kornell-Lindenhovius-Mislove (2024) §3.3.

---

## `src/theory/` — Proofs and Constructions

All files import from `DomainTheory.structures`. Dune library:
`DomainTheory.theory`.

---

### `OrderTheory.v` ✓ (Phase 0) — 480 lines

**Imports:** `Order`

| Name | Kind | Description |
|------|------|-------------|
| `pequiv_refl/symm/trans` | Lemmas | `≈` is an equivalence relation |
| `pequiv_iff_eq` | Lemma | In a `PartialOrder`, `x ≈ y ↔ x = y` |
| `le_antisym_unique` | Lemma | alias for `le_antisym` with explicit name |
| `chain_mono_le` | Lemma | `m ≤ n → c.[m] ⊑ c.[n]` |
| `chain_le_trans` | Lemma | transitivity along a chain via index |
| `mono_preserves_equiv` | Lemma | `f` monotone, `x ≈ y → f x ≈ f y` |
| `map_chain_ext_equiv` | Lemma | pointwise `≈` implies `map_chain` equivalence |

---

### `ChainTheory.v` ✓ (Phase 0) — 498 lines

**Imports:** `Order`, `OrderTheory`

| Name | Kind | Description |
|------|------|-------------|
| `chain_shift k c` | Definition | `n ↦ c.[n + k]`: shift a chain by `k` |
| `chain_shift_index/zero/succ/add/ge` | Lemmas | computation and monotonicity lemmas for `chain_shift` |
| `map_chain_shift` | Lemma | shift commutes with `map_chain` |
| `eventually_const c x` | Definition | `∃ N, ∀ n ≥ N, c.[n] = x` |
| `eventually_const_*` | Lemmas | closure properties of `eventually_const` |
| `chain_pred_stabilises` | Lemma | a boolean predicate on a chain either stabilises at `true` or stays `false` (uses `Classical`) |
| `chain_pred_dichotomy` | Lemma | `φ (c.[0]) = true` or `φ (c.[0]) = false` and stability |
| `coherent_family_const` | Lemma | the constant family is coherent |

---

### `CPOTheory.v` ✓ (Phase 0) — 556 lines

**Imports:** `CPO`, `Morphisms`, `OrderTheory`, `ChainTheory`

| Name | Kind | Description |
|------|------|-------------|
| `sup_unique` | Lemma | sup is uniquely determined by upper bound + minimality |
| `sup_le_iff` | Lemma | `x ⊑ ⊔ c ↔ ∃ n, x ⊑ c.[n]` |
| `le_sup_of_le_elem` | Lemma | `x ⊑ c.[n] → x ⊑ ⊔ c` |
| `sup_const_chain` | Lemma | `⊔ (const_chain x) = x` |
| `sup_tail`, `sup_shift` | Lemmas | sup is shift-invariant |
| `sup_eventually_const` | Lemma | `eventually_const c x → ⊔ c = x` |
| `sup_equiv` | Lemma | pointwise `≈` implies equal sups |
| `sup_ext` | Lemma | pointwise `=` implies equal sups |
| `mono_sup_le` | Lemma | `f` monotone → `f (⊔ c) ≥ ⊔ (map_chain f c)` |
| `continuous_iff_le` | Lemma | `f` continuous ↔ `f (⊔ c) ⊑ ⊔ (map_chain f c)` |
| `cont_fun_ext` | Lemma | continuous function extensionality |
| `cont_apply_sup` | Lemma | `f (⊔ c) = ⊔ (map_chain f c)` for continuous `f` |

---

### `ScottTopology.v` ✓ (Phase 0) — 512 lines

**Imports:** `CPO`, `Morphisms`, `CPOTheory`, `Classical`

| Name | Kind | Description |
|------|------|-------------|
| `waybelow x y` (`x ≪ y`) | Definition | `x` is way-below `y`: `∀ chains c, y ⊑ ⊔ c → ∃ n, x ⊑ c.[n]` |
| `waybelow_le` | Lemma | `x ≪ y → x ⊑ y` |
| `waybelow_trans/le_r/le_l/mono` | Lemmas | closure properties of `≪` |
| `waybelow_bottom` | Lemma | `⊥ ≪ x` for all `x` in any `PointedCPO` |
| `compact x` | Definition | `x ≪ x` |
| `compact_le_sup` | Lemma | compact elements reach the sup of any chain they're below |
| `scott_open U` | Definition | upward-closed and inaccessible by chain sups |
| `scott_open_inter/union` | Lemmas | Scott topology is closed under finite intersection and arbitrary union |
| `complement_downset_scott_open` | Lemma | `{y | ¬(y ⊑ x)}` is Scott-open |

---

### `FixedPoints.v` ✓ (Phase 0) — 494 lines

**Imports:** `CPO`, `Morphisms`, `CPOTheory`, `OrderTheory`, `ChainTheory`\
**Context:** `D : PointedCPO.type`

| Name | Kind | Description |
|------|------|-------------|
| `iter f n` | Definition | `fⁿ(⊥)`: n-th Kleene iterate |
| `iter_succ_le` | Lemma | `fⁿ(⊥) ⊑ fⁿ⁺¹(⊥)` |
| `iter_mono` | Lemma | `m ≤ n → iter f m ⊑ iter f n` |
| `kleene_chain f` | Definition | the chain `⊥, f(⊥), f²(⊥), ...` |
| `fixp f` | Definition | `⊔ (kleene_chain f)`: the least fixed point |
| `fixp_is_fixedpoint` | Theorem | `f (fixp f) = fixp f` |
| `fixp_least` | Theorem | `fixp f` is the least pre-fixed point |
| `fixp_unfold` | Lemma | `fixp f = f (fixp f)` (useful for rewriting) |
| `fixp_ind` | Theorem | induction principle for admissible predicates |
| `iter_satisfies` | Lemma | if `P` is admissible and `P ⊥`, then `P (iter f n)` for all `n` |

The internalized `FIXP : (D ⇒c D) →c D` is deferred to `FunctionSpaces.v`.

Reference: A&J §2.1.3. Benton-Kennedy §2.1 (`fixp`, `FIXP`, `fixp_ind`).

---

### `Products.v` ✓ (Phase 0) — 519 lines

**Imports:** `CPO`, `Morphisms`, `CPOTheory`

| Name | Kind | Description |
|------|------|-------------|
| `prod_le` | Definition | componentwise order on `D * E` |
| `prod_sup` | Definition | componentwise sup |
| `π₁`, `π₂` | Definitions | continuous projections |
| `cont_pair f g` | Definition | continuous pairing `⟨f, g⟩ : C →c D * E` |
| `cont_prod_map` | Definition | functorial action on morphisms |
| `cont_swap` | Definition | `D * E →c E * D` |
| `prod_pointed` | Instance | `D * E` is a `PointedCPO` when both factors are |
| Universal property | Lemmas | `cont_pair_fst/snd`, uniqueness |

Note: `D * E` is a `CPO`; it is a `PointedCPO` when both `D` and `E` are.

Reference: A&J §3.2.1. Benton-Kennedy §2.1.

---

### `Sums.v` ✓ (Phase 0) — 611 lines

**Imports:** `CPO`, `Morphisms`, `CPOTheory`

| Name | Kind | Description |
|------|------|-------------|
| `sum_le` | Definition | separated sum order on `D + E` |
| `chain_inl_stable`, `chain_inr_stable` | Lemmas | chains cannot cross summands |
| `extract_left_mfun`, `extract_right_mfun` | Definitions | monotone projections with default |
| `sum_sup` | Definition | componentwise sup using chain stability |
| `ι₁`, `ι₂` | Definitions | continuous injections `inl` and `inr` |
| `sum_case f g` | Definition | copairing `[f,g] : D+E →c F` |
| `sum_case_unique` | Lemma | universal property: uniqueness |

Note: `D + E` is deliberately **not** a `PointedCPO` even when both summands
are: `inl ⊥` and `inr ⊥` are incomparable. For a pointed sum, use `(D+E)⊥`.
The sup proof is constructive — no classical axioms.

Reference: Benton-Kennedy §2.1.

---

### `Lift.v` ✓ (Phase 0) — 600 lines

**Imports:** `CPO`, `Morphisms`, `CPOTheory`, `ChainTheory`, `ClassicalEpsilon`

| Name | Kind | Description |
|------|------|-------------|
| `lift_le` | Definition | flat lift order on `option D` |
| `D_chain_fn N d₀ c k` | Definition | extract `D`-value from `c.[N+k]`; default `d₀` unreachable |
| `D_chain N d₀ c HN` | Definition | the `chain D` extracted from a converged `option D` chain |
| `chain_some_stable` | Lemma | once a chain reaches `Some`, it stays in `Some` |
| `lift_sup` | Definition | `option D` sup via `ClassicalEpsilon` |
| `lift_sup_some_eq` | Lemma | key: `⊔ c = Some (⊔ D_chain N d₀ c HN)` when `c.[N] ≠ None` |
| `lift_bottom_least` | Lemma | `None ⊑ x` for all `x` |
| `ret` | Definition | unit `d ↦ Some d`, proved continuous |
| `kleisli f` | Definition | Kleisli extension `D⊥ →c E⊥`, proved continuous |
| `kleisli_ret_left/right` | Lemmas | ML1, ML2 monad laws |
| `kleisli_assoc` | Lemma | ML3 monad law |

**HB instance order:** `lift_IsCPO` must precede `lift_HasBottom` and
`lift_IsPointed`. See `migration-notes.md § Lift.v`.

**Axiom use:** `ClassicalEpsilon` only (beyond `Classical.v`). No admits.

Reference: A&J §2.1.4. Moggi (1991). Benton-Kennedy §2.2.

---

### `LiftMonad.v` ✓ (Phase 0, supplementary) — 476 lines

**Imports:** none (self-contained)

| Name | Kind | Description |
|------|------|-------------|
| `delay D` | CoInductive | `now d \| later t`; the delay monad carrier |
| `delay_decompose` | Definition | "frob" trick: forces one cofix evaluation step |
| `bisim t1 t2` | CoInductive | weak bisimulation: `t1` and `t2` converge to the same value |
| `bisim_refl/sym` | CoFixpoints | reflexivity and symmetry of `bisim` |
| `bisim_trans` | Lemma | transitivity — **partially admitted** (guardedness failure) |
| `bot` | CoFixpoint | the diverging computation `later (later (...))` |
| `bot_unfold` | Lemma | `bot = later bot` (uses `delay_decompose`) |
| `bind t f` | CoFixpoint | monadic bind / Kleisli sequencing |
| `bind_now`, `bind_later` | Lemmas | computation rules (use frob trick) |
| `bind_right_unit`, `bind_assoc`, `bind_compat` | Lemmas | monad laws up to `bisim` |
| `converges t d` | Inductive | `t` terminates with value `d` after finitely many `later` steps |
| `converges_bisim` | Lemma | preservation — **partially admitted** (coinductive inversion) |
| `bot_not_converges` | Lemma | `bot` never converges (uses `bot_unfold`) |
| `fact_A/B/C` | Lemmas | the three components of the CPO obstruction |
| `delay_CPO_requires_quotient` | Theorem | `delay D` cannot be `CPO.type` without quotienting by `bisim` |

**Purpose:** (1) thesis exposition of the coinductive alternative; (2) precise
statement of why quotient types are required. See `design-decisions.md § DD-006`
and `§ DD-007`.

---

### `EnrichedTheory.v` ✗ (Phase 1) — *not yet written*

**Imports:** `Enriched`, `CPOTheory`, `FunctionSpaces`

Planned: enriched natural transformations, A&J Proposition 5.2.4,
Yoneda in the enriched setting.

---

### `NatTrans.v` ✗ (Phase 1) — *not yet written*

**Imports:** `Enriched`, `EnrichedTheory`

Planned: enriched natural transformations as a CPO (pointwise order),
horizontal and vertical composition.

---

### `FunctionSpaces.v` ✗ (Phase 0) — *not yet written*

**Imports:** `CPO`, `Morphisms`, `CPOTheory`, `Products`

Planned: function-space CPO `D ⇒ E` with pointwise order, `curry`,
`uncurry`, `ev`. Proof that `CPO` is Cartesian closed. Internalized
`FIXP : (D ⇒c D) →c D` using the fixed-point theory from `FixedPoints.v`.

Reference: A&J §3.2.2. Benton-Kennedy §2.1.

---

### `DomainEquations.v` ✗ (Phase 0/1) — *not yet written*

**Imports:** `Enriched`, `Products`, `FunctionSpaces`, `Lift`,
`EnrichedTheory`

Planned: `IsMixedLocallyContinuous` mixin; embedding-projection pairs;
bilimit / inverse-limit construction; proof `D ≅ [D → D]⊥`.

Reference: A&J §5.2–5.3. Benton-Kennedy §4. Pitts (1996).

---

## `src/instances/` — Concrete Instance Registrations

All files import from both `DomainTheory.structures` and
`DomainTheory.theory`. Dune library: `DomainTheory.instances`.

| File | Phase | Registers |
|------|-------|-----------|
| `Nat.v` | 0 | `nat` with `≤` as `CPO.type` |
| `Discrete.v` | 0 | `Discrete X` (equality order) as `CPO.type` |
| `Lift.v` | 0 | `D⊥` as `PointedCPO.type` |
| `Product.v` | 0 | `D × E` as `CPO.type`; `PointedCPO.type` when both pointed |
| `Sum.v` | 0 | `D + E` as `CPO.type` |
| `Function.v` | 0/1 | `D ⇒ E` as `CPO.type`; `CPO.type` as `CPOEnrichedCat` |
| `Quantum.v` | 2 | qCPO instances (stretch goal) |

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
              ├── ScottTopology.v    ← CPOTheory, Classical
              ├── FixedPoints.v      ← CPOTheory
              ├── Products.v         ← CPOTheory
              ├── Sums.v             ← CPOTheory
              ├── Lift.v             ← CPOTheory, ClassicalEpsilon
              ├── LiftMonad.v        ← (self-contained; no imports)
              ├── FunctionSpaces.v   ← Products           [not written]
              ├── EnrichedTheory.v   ← Enriched, FunctionSpaces  [not written]
              ├── NatTrans.v         ← EnrichedTheory     [not written]
              └── DomainEquations.v  ← Enriched, Products,
                                        FunctionSpaces, Lift,
                                        EnrichedTheory     [not written]
```

---

## Line Count Summary

| File | Lines | Status |
|------|-------|--------|
| `src/structures/Order.v` | 195 | ✓ Done |
| `src/structures/CPO.v` | 187 | ✓ Done |
| `src/structures/Morphisms.v` | 203 | ✓ Done |
| `src/structures/Enriched.v` | 388 | ✓ Done |
| **Structures subtotal** | **973** | |
| `src/theory/OrderTheory.v` | 480 | ✓ Done |
| `src/theory/ChainTheory.v` | 498 | ✓ Done |
| `src/theory/CPOTheory.v` | 556 | ✓ Done |
| `src/theory/ScottTopology.v` | 512 | ✓ Done |
| `src/theory/FixedPoints.v` | 494 | ✓ Done |
| `src/theory/Products.v` | 519 | ✓ Done |
| `src/theory/Sums.v` | 611 | ✓ Done |
| `src/theory/Lift.v` | 600 | ✓ Done |
| `src/theory/LiftMonad.v` | 476 | ✓ Done (supplementary) |
| `src/theory/FunctionSpaces.v` | — | ✗ Not written |
| `src/theory/EnrichedTheory.v` | — | ✗ Not written |
| `src/theory/NatTrans.v` | — | ✗ Not written |
| `src/theory/DomainEquations.v` | — | ✗ Not written |
| **Theory subtotal (written)** | **4,746** | |
| `src/instances/` (all files) | — | ✗ Not written |
| `src/lang/` (all files) | — | ✗ Not written |
| **Grand total (written)** | **5,719** | |

Thesis target for Phase 0+1 total: ~7,000–8,000 lines of specification.