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
DomainTheory.Structures
  └── DomainTheory.Theory
        └── DomainTheory.Instances
              └── DomainTheory.Lang / DomainTheory.Quantum
```

---

## Phase Map

| Phase | Scope | Status |
|-------|-------|--------|
| 0 | Modernize Benton-Kennedy library (CPOs, constructions, fixed points, lift) | **Complete** (structures + core theory + instances) |
| 1 | Enriched categories, locally continuous functors, PCF adequacy | **Complete**: Structures, EnrichedTheory, NatTrans, DomainEquations, Yoneda, PCF pipeline all done |
| 2 | Quantum CPO structures (stretch goal) | **In progress**: QuantumStructure.v (339 lines, L1 complete), qCPO.v (388 lines, L2 complete), qCPOProperties.v (1022 lines, L3 complete); QuantumMorphisms.v (L4), QuantumEnrichment.v (L5) remain stubs |
| 3 | QMini-Core language prototype (stretch goal) | Not started |

---

## `src/structures/` — Structure Declarations

All files contain **only** HB mixin and structure declarations — no
proofs, no lemmas. Dune library: `DomainTheory.Structures`.

> **Note on `Pointed.v`:** There is no `Pointed.v`. `HasBottom`, `IsPointed`,
> and `PointedCPO` live in `CPO.v`; `strict_fun` lives in `Morphisms.v`.
> See `docs/design-decisions.md § DD-001`.

---

### `Order.v` ✓ (Phase 0) — 191 lines

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

### `CPO.v` ✓ (Phase 0) — 182 lines

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

### `Morphisms.v` ✓ (Phase 0) — 234 lines

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

### `Enriched.v` ✓ (Phase 1) — 378 lines

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

All files import from `DomainTheory.Structures`. Dune library:
`DomainTheory.Theory`.

---

### `OrderTheory.v` ✓ (Phase 0) — 494 lines

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

### `ChainTheory.v` ✓ (Phase 0) — 515 lines

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

### `CPOTheory.v` ✓ (Phase 0) — 585 lines

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

### `ScottTopology.v` ✓ (Phase 0) — 519 lines

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

### `FixedPoints.v` ✓ (Phase 0) — 525 lines

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

The internalized `FIXP : (D ⇒c D) →c D` lives in `FunctionSpaces.v` §6.

Reference: A&J §2.1.3. Benton-Kennedy §2.1 (`fixp`, `FIXP`, `fixp_ind`).

---

### `Products.v` ✓ (Phase 0) — 537 lines

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

### `Sums.v` ✓ (Phase 0) — 624 lines

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

### `Lift.v` ✓ (Phase 0) — 647 lines

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

### `LiftMonad.v` ✓ (Phase 0, supplementary) — 488 lines

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

### `EnrichedTheory.v` ✓ (Phase 1) — 706 lines

**Imports:** `Order`, `CPO`, `Morphisms`, `Enriched`, `OrderTheory`,
`ChainTheory`, `CPOTheory`, `Products`, `FunctionSpaces`

| Name | Kind | Description |
|------|------|-------------|
| `comp_cont_l_eq` | Lemma | `f ⊚ (⊔ c) = ⊔ (map_chain (comp_l_cont_fun f) c)` |
| `comp_cont_r_eq` | Lemma | `(⊔ c) ⊚ g = ⊔ (map_chain (comp_r_cont_fun g) c)` |
| `F_mor_sup_eq` | Lemma | `F_mor (⊔ c) = ⊔ (map_chain F_mor_cont_fun c)` |
| `comp_chain` | Definition | chain of compositions `f.[n] ⊚ g.[n]` |
| `comp_joint_sup` | Lemma | `⊔ comp_chain = (⊔ fs) ⊚ (⊔ gs)` (product-free) |
| `comp_joint_continuous` | Lemma | composition is jointly Scott-continuous |
| `comp_joint_cont_fun` | Definition | joint composition as `cont_fun` |
| `comp_joint_apply` | Lemma | computation rule for `comp_joint_cont_fun` |
| `lc_functor` | Record | plain record for locally continuous endofunctors |
| `lc_functor_of_hb` | Definition | convert HB `LocallyContinuousFunctor` to `lc_functor` |
| `lc_functor_mor_eq` | Lemma | `lcf_mor` preserves chain sups |
| `id_lc_functor` | Definition | identity endofunctor |
| `comp_lc_functor` | Definition | composition of LC functors |
| `ep_pair` | Record | embedding-projection pair with retraction + deflation |
| `ep_id` | Definition | identity EP-pair |
| `ep_comp` | Definition | composition of EP-pairs |
| `ep_emb_mono` | Lemma | embeddings preserve order |
| `ep_proj_mono` | Lemma | projections preserve order |
| `ep_proj_emb_cancel` | Lemma | EP-pair cancellation |
| `ep_chain` | Record | ω-sequence of EP-pairs with accessors |

Proof strategy: §2 uses a two-stage approach (product-free core +
product packaging) to avoid HB coercion conflicts. See DD-016.

Reference: A&J §5.2. Benton-Kennedy §4.

---

### `NatTrans.v` ✓ (Phase 1) — 518 lines

**Imports:** `Order`, `CPO`, `Morphisms`, `Enriched`,
`OrderTheory`, `CPOTheory`, `EnrichedTheory`

| Name | Kind | Description |
|------|------|-------------|
| `nat_trans F G` | Record | enriched natural transformation: components + naturality |
| `nt_component` | Accessor | component of a nat trans at an object |
| `nt_naturality` | Accessor | naturality square: `G(f) ∘ α_X = α_Y ∘ F(f)` |
| `nt_id F` | Definition | identity natural transformation (components = `id_mor`) |
| `nt_vcomp β α` | Definition | vertical composition (componentwise `β_X ∘ α_X`) |
| `nt_lwhisker H α` | Definition | left whiskering `H * α` (apply `H` to components) |
| `nt_rwhisker α H` | Definition | right whiskering `α * H` |
| `nt_le` | Definition | pointwise order on components |
| `nt_le_refl/trans/antisym` | Lemmas | partial order on nat trans |
| `nt_chain_component` | Definition | extract a chain in hom-CPO from chain of nat trans |
| `nt_sup` | Definition | pointwise supremum of a chain of nat trans |
| `nt_sup_upper/least` | Lemmas | CPO axioms for nat trans |
| `nt_interchange` | Lemma | `(β' · β) * (α' · α) = (β' * α') · (β * α)` |

Design: uses `lc_functor` plain record to avoid universe inconsistencies.
0 Admitted. See DD-018.

Reference: Kelly (1982) Ch. 1. Mac Lane (1998) Ch. IX. A&J §5.2.

---

### `FunctionSpaces.v` ✓ (Phase 0) — 882 lines

**Imports:** `Order`, `CPO`, `Morphisms`, `OrderTheory`, `ChainTheory`,
`CPOTheory`, `Products`, `FixedPoints`

| Name | Kind | Description |
|------|------|-------------|
| `fun_le` | Definition | pointwise order on `cont_fun D E` |
| `fun_le_refl/trans/antisym` | Lemmas | `fun_le` is a partial order |
| `fun_HasLe/IsPreorder/IsPartialOrder` | HB instances | `cont_fun D E` is a `PartialOrder` |
| `eval_at_mono` | Definition | `x ↦ f(x)` is monotone in `f` for fixed `x` |
| `pointwise_chain` | Definition | `n ↦ fs.[n](x)`: chain in `E` from a chain of functions |
| `fun_sup_fun` | Definition | `λ x. ⊔_n fs.[n](x)`: pointwise sup |
| `fun_sup_mono` | Lemma | pointwise sup is monotone |
| `fun_sup_continuous` | Lemma | pointwise sup is continuous (key: double-sup commutativity) |
| `fun_sup` | Definition | pointwise sup packaged as `cont_fun D E` |
| `fun_sup_upper/least` | Lemmas | sup axioms for `fun_sup` |
| `fun_HasSup`, `fun_IsCPO` | HB instances | `cont_fun D E` is a `CPO` |
| `fun_bottom` | Definition | `λ x. ⊥`: constant bottom function |
| `fun_HasBottom`, `fun_IsPointed` | HB instances | `cont_fun D E` is a `PointedCPO` when `E` is |
| `cont_eval` | Definition | evaluation map `ev : (D ⇒ E) × D →c E` |
| `cont_curry` | Definition | currying `(C × D →c E) → (C →c D ⇒ E)` |
| `cont_uncurry` | Definition | uncurrying `(C →c D ⇒ E) → (C × D →c E)` |
| `curry_uncurry`, `uncurry_curry` | Lemmas | curry/uncurry are inverse |
| `curry_comp` | Lemma | functoriality: `curry(f) ∘ g = curry(f ∘ (g × id))` |
| `eval_curry` | Lemma | `ev ∘ (curry(f) × id) = f` |
| `curry_unique` | Lemma | universal property of the exponential |
| `fun_sup_const`, `sup_apply`, `sup_chain_apply_le` | Lemmas | miscellaneous function-space sup lemmas |
| `fixp_mono_fun` | Definition | `fixp` as a monotone map on `[D →c D]` |
| `fixp_chain` | Definition | `n ↦ fixp(fs.[n])`: chain of fixpoints |
| `sup_fixp_prefixed` | Lemma | `⊔_n fixp(f_n)` is a pre-fixed-point of `⊔_n f_n` |
| `fixp_continuous` | Lemma | `fixp` is Scott-continuous on the function-space |
| `FIXP` | Definition | `[[D →c D] →c D]`: the continuous fixed-point operator |
| `FIXP_eq`, `FIXP_is_fixedpoint` | Lemmas | computation rule and fixed-point property |
| `FIXP_least`, `FIXP_least_fixedpoint` | Lemmas | least (pre-)fixed-point properties |
| `FIXP_ind` | Lemma | fixed-point induction via `FIXP` |

Note: `cont_fun D E` is a `CPO` for all `D E : CPO.type`; it is a
`PointedCPO` when `E : PointedCPO.type`. `FIXP : [[D →c D] →c D]`
packages the Kleene fixed-point as a continuous operator on the
function-space CPO.

Reference: A&J §2.1.3, §3.2.2. Benton-Kennedy §2.1.

---

### `DomainEquations.v` ✓ (Phase 0/1) — 446 lines

**Imports:** `Order`, `CPO`, `Morphisms`, `Enriched`, `OrderTheory`,
`ChainTheory`, `CPOTheory`, `Products`, `FunctionSpaces`, `EnrichedTheory`,
`PeanoNat`

| Name | Kind | Description |
|------|------|-------------|
| `IsMixedLocallyContinuous` | HB mixin | 6 axioms: identity, composition, separate mono + cont |
| `MixedLCFunctor` | HB structure | bundled mixed-variance LC bifunctor |
| `mf_mor` | Definition | wrapper pinning carrier to `MixedLCFunctor.type` |
| `MF_mor_l_cont_fun` | Definition | left variable as `cont_fun` |
| `MF_mor_r_cont_fun` | Definition | right variable as `cont_fun` |
| `MF_mor_cont_l_eq/r_eq` | Lemmas | equational rewrites for continuity |
| `MF_mor_mono` | Lemma | joint monotonicity (derived from separate) |
| `mf_diag_chain` | Definition | diagonal chain from two chains |
| `mf_diag_bound` | Lemma | diagonal elements bounded by sup |
| `MF_mor_joint_sup` | Theorem | `mf_mor (⊔ fs) (⊔ gs) = ⊔ (mf_diag_chain fs gs)` |
| `MF_mor_id_both` | Lemma | identity on both arguments |
| `mf_ep_pair` | Definition | EP-pair lifting (A&J Prop. 5.2.6) |
| `mf_ep_emb/proj` | Lemmas | unfolding lemmas for lifted EP-pair |
| `mf_ep_comp_emb/proj` | Lemmas | compatibility with EP-pair composition |
| `mf_approx_obj` | Fixpoint | `D_n = F^n(D_0)` approximation objects |
| `mf_approx_ep` | Fixpoint | EP-pairs `D_n ↪ D_{n+1}` |
| `mf_approx_epc` | Definition | approximation sequence as `ep_chain` |
| `BilimitData` | Record | bilimit cone: emb/proj, compatibility, roll/unroll |
| `bilimit_exists` | Axiom | existence of bilimit (requires omega-product CPO) |
| `D_inf` | Definition | the bilimit object `D_∞` |
| `ROLL` / `UNROLL` | Definitions | isomorphism `F(D_∞, D_∞) ≅ D_∞` |
| `bil_iso_roll_unroll` | Theorem | `ROLL ∘ UNROLL = id` |
| `bil_iso_unroll_roll` | Theorem | `UNROLL ∘ ROLL = id` |
| `bil_defl_chain` | Definition | chain of deflations `emb_n ∘ proj_n` |
| `bil_sup_deflations` | Lemma | `⊔ bil_defl_chain = id` |
| `bil_lim_iso` | Definition | `D_∞ ≅ F(D_∞, D_∞)` as `ep_pair` |
| `bil_cone_ep` | Definition | cone EP-pairs `D_n ↪ D_∞` |

0 Admitted; 1 Axiom (`bilimit_exists`). See DD-017.

Reference: A&J §5.2–5.3. Benton-Kennedy §4. Smyth & Plotkin (1982).

---

## `src/instances/` — Concrete Instance Registrations

All files import from both `DomainTheory.Structures` and
`DomainTheory.Theory`. Dune library: `DomainTheory.Instances`.

| File | Phase | Lines | Status |
|------|-------|-------|--------|
| `Nat.v` | 0 | 371 | ✓ Done |
| `Discrete.v` | 0 | 531 | ✓ Done |
| `Function.v` | 0/1 | 436 | ✓ Done (CPO self-enrichment + utilities) |
| `Yoneda.v` | 1 | 443 | ✓ Done (representable functor + Yoneda lemma) |
| `FunLift.v` | 1 | 298 | ✓ Done (MixedLCFunctor instance for lifted function-space bifunctor) |
| `Quantum.v` | 2 | 5 | Stub (stretch goal) |

> **Note:** The Lift, Product, and Sum CPO instances are registered
> directly in `theory/Lift.v`, `theory/Products.v`, and `theory/Sums.v`
> respectively; separate instance files for these types were removed on
> 2026-03-04.

---

## `src/lang/` — Language Semantics

Dune library: `DomainTheory.Lang`. Depends on `DomainTheory.Instances`.

| File | Phase | Lines | Description |
|------|-------|-------|-------------|
| `PCF_Syntax.v` | 1 | 804 | ✓ Intrinsic typed ANF: Ty, Var, Value/Exp, renamings, substitutions |
| `PCF_Operational.v` | 1 | 332 | ✓ Big-step CBV evaluation `e ⇓ v`, determinism, inversion lemmas |
| `PCF_Denotational.v` | 1 | 1,167 | ✓ Denotation, combinators, computation rules, renaming + substitution lemmas (0 Admitted) |
| `PCF_Soundness.v` | 1 | 261 | ✓ `e ⇓ v → sem_exp e tt = Some (sem_val v tt)`, corollaries (0 Admitted) |
| `PCF_Adequacy.v` | 1 | 820 | ✓ Computational adequacy via logical relation, fundamental lemma, full correspondence (0 Admitted) |
| `QMiniCore_Syntax.v` | 2/3 | 9 | Stub: quantum lambda calculus syntax |
| `QMiniCore_Semantics.v` | 2/3 | 9 | Stub: quantum denotational semantics |

---

## `examples/` -- Worked Examples

Pedagogical example files demonstrating the library's main constructions.
All compile clean as of 2026-03-13.

| File | Lines | Description |
|------|-------|-------------|
| `basic_cpos.v` | 347 | Guided tour: unit (S1), nat_inf (S2), discrete bool (S3), products (S4), lift (S5), function spaces (S6), Kleene fixed-point (S7). Demonstrates chains, sups, order, continuity, `fixp`. |
| `enriched_usage.v` | 234 | CPO-enriched category toolkit: category axioms (S1), composition continuity (S2), representable functor `Hom(X,-)` (S3), natural transformations (S4), EP-pairs (S5). Uses abstract `Context {C : CPOEnrichedCat.type}`. |
| `pcf_examples.v` | 226 | Full PCF pipeline: base expressions with literals/arithmetic/comparison/if (S1), function application with identity/constant/double via `FIX` (S2), denotational semantics for base cases (S3), soundness (S4), adequacy + convergence_iff_defined (S5). |
| `recursive_domain.v` | 179 | Bilimit machinery: abstract ROLL/UNROLL isomorphism (S1), concrete lifted function-space functor FL on CPO.type with unit initial EP-pair (S2), approximation tower levels 0/1/2 (S3), deflation chain below id with sup = id completeness (S4). |
| **Examples subtotal** | **986** | |

---

## `src/quantum/` — Quantum CPO Structures (Phase 2)

Dune library: `DomainTheory.Quantum`. Depends on `DomainTheory.Structures`.

Design: Atoms-only representation with axiomatic involutive quantale (Option B+
from `planning/quantum.md`). See DD-022. Quantum sets = plain Types;
quantum relations = Q-valued functions where Q is an HB `InvQuantale`.
No Hilbert spaces or operator algebras.

| File | Phase | Lines | Status | Description |
|------|-------|-------|--------|-------------|
| `QuantumStructure.v` | 2 (L1) | 339 | ✓ Done | `desc_chain`, `HasQuantaleOps` + `IsInvQuantale` HB hierarchy, `q_delta`, `qposet` record, `qp_antitone_l` |
| `qCPO.v` | 2 (L2) | 388 | ✓ Done | `qchain`, `converges`/`converges_eq`, `is_qcpo`/`QCPOData`, `q_monotone`, `map_qchain`, `q_scott_continuous`, `is_pointed_qcpo`, constant chain convergence |
| `qCPOProperties.v` | 2 (L3) | 1,022 | ✓ Done | `q_cont_fun` bundled maps (DD-023), `q_cont_id`/`q_cont_const`/`q_cont_comp`, category laws, cofinal subsequences, `q_hom_le` pointwise order, CPO-enrichment (`qhom_limit_cont`), Kleene fixed point (`qfixp_at`, Scott induction); 32 Qed, 0 Admitted |
| `QuantumMorphisms.v` | 2 (L4) | 9 | Stub (stretch) | Lift monad (-)⊥, Kleisli category, strict maps |
| `QuantumEnrichment.v` | 2 (L5) | 9 | Stub (stretch) | Classical embedding '(-) : CPO → qCPO, CPO-enrichment |

References: Kornell, Lindenhovius & Mislove (2024) "Categories of Quantum CPOs".

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
              ├── FunctionSpaces.v   ← Products, FixedPoints
              ├── EnrichedTheory.v   ← Enriched, Products, FunctionSpaces
              ├── NatTrans.v         ← EnrichedTheory
              └── DomainEquations.v  ← Enriched, Products,
                                        FunctionSpaces,
                                        EnrichedTheory

[instances/]
  ├── Nat.v              ← CPOTheory, ChainTheory
  ├── Discrete.v         ← CPOTheory, ChainTheory
  ├── Function.v         ← Enriched, FunctionSpaces, Morphisms
  ├── Yoneda.v           ← NatTrans, Function, EnrichedTheory
  └── FunLift.v          ← Function, FunctionSpaces, Lift, DomainEquations

[lang/]
  ├── PCF_Syntax.v       ← (Stdlib only)
  ├── PCF_Operational.v  ← PCF_Syntax
  ├── PCF_Denotational.v ← PCF_Syntax, FunctionSpaces, Lift, FixedPoints, Discrete, Function
  ├── PCF_Soundness.v    ← PCF_Operational, PCF_Denotational
  └── PCF_Adequacy.v     ← PCF_Soundness, Lift, FixedPoints, FunctionSpaces, CPOTheory, Classical

[quantum/]
  ├── QuantumStructure.v ← Order (PartialOrder)
  ├── qCPO.v             ← QuantumStructure
  ├── qCPOProperties.v   ← qCPO, QuantumStructure, ProofIrrelevance, FunctionalExtensionality
  ├── QuantumMorphisms.v ← qCPO, QuantumStructure  (stub)
  └── QuantumEnrichment.v← qCPO, Enriched          (stub)
```

---

## Line Count Summary

| File | Lines | Status |
|------|-------|--------|
| `src/structures/Order.v` | 191 | ✓ Done |
| `src/structures/CPO.v` | 182 | ✓ Done |
| `src/structures/Morphisms.v` | 234 | ✓ Done |
| `src/structures/Enriched.v` | 378 | ✓ Done |
| **Structures subtotal** | **985** | |
| `src/theory/OrderTheory.v` | 494 | ✓ Done |
| `src/theory/ChainTheory.v` | 515 | ✓ Done |
| `src/theory/CPOTheory.v` | 585 | ✓ Done |
| `src/theory/ScottTopology.v` | 519 | ✓ Done |
| `src/theory/FixedPoints.v` | 525 | ✓ Done |
| `src/theory/Products.v` | 537 | ✓ Done |
| `src/theory/Sums.v` | 624 | ✓ Done |
| `src/theory/Lift.v` | 647 | ✓ Done |
| `src/theory/LiftMonad.v` | 488 | ✓ Done (supplementary) |
| `src/theory/FunctionSpaces.v` | 882 | ✓ Done |
| `src/theory/EnrichedTheory.v` | 706 | ✓ Done |
| `src/theory/NatTrans.v` | 518 | ✓ Done |
| `src/theory/DomainEquations.v` | 446 | ✓ Done (1 Axiom) |
| **Theory subtotal** | **7,486** | |
| `src/instances/Nat.v` | 371 | ✓ Done |
| `src/instances/Discrete.v` | 531 | ✓ Done |
| `src/instances/Function.v` | 436 | ✓ Done |
| `src/instances/Yoneda.v` | 443 | ✓ Done |
| `src/instances/FunLift.v` | 298 | ✓ Done |
| `src/instances/Quantum.v` | 5 | Stub |
| **Instances subtotal** | **2,084** | |
| `src/lang/PCF_Syntax.v` | 804 | ✓ Done |
| `src/lang/PCF_Operational.v` | 332 | ✓ Done |
| `src/lang/PCF_Denotational.v` | 1,167 | ✓ Done (0 Admitted) |
| `src/lang/PCF_Soundness.v` | 261 | ✓ Done |
| `src/lang/PCF_Adequacy.v` | 820 | ✓ Done |
| `src/lang/QMiniCore_Syntax.v` | 9 | Stub |
| `src/lang/QMiniCore_Semantics.v` | 9 | Stub |
| **Lang subtotal** | **3,402** | |
| `src/quantum/QuantumStructure.v` | 339 | ✓ Done |
| `src/quantum/qCPO.v` | 388 | ✓ Done |
| `src/quantum/qCPOProperties.v` | 1,022 | ✓ Done |
| `src/quantum/QuantumMorphisms.v` | 9 | Stub |
| `src/quantum/QuantumEnrichment.v` | 9 | Stub |
| **Quantum subtotal** | **1,767** | |
| `test/LiftTests.v` | 295 | ✓ Done |
| `test/EnrichedTests.v` | 194 | ✓ Done |
| `test/FixedPointTests.v` | 290 | ✓ Done |
| `test/FunctionSpaceTests.v` | 193 | ✓ Done |
| `test/PCFTests.v` | 242 | ✓ Done |
| `test/ProductTests.v` | 184 | ✓ Done |
| `test/SumTests.v` | 181 | ✓ Done |
| **Tests subtotal** | **1,579** | |
| `examples/basic_cpos.v` | 347 | ✓ Done |
| `examples/enriched_usage.v` | 234 | ✓ Done |
| `examples/pcf_examples.v` | 226 | ✓ Done |
| `examples/recursive_domain.v` | 179 | ✓ Done |
| **Examples subtotal** | **986** | |
| **Grand total** | **18,289** |

Thesis target for Phase 0+1 total: ~7,000–8,000 lines of specification.
Actual: ~18,289 lines (exceeds target; includes 986 lines of worked examples,
1,579 lines of tests, and 1,767 lines of quantum CPO structures).

> **Note:** Line counts as of 2026-03-19. Quantum files add 1,731 net lines
> (QuantumStructure.v 339 + qCPO.v 388 + qCPOProperties.v 1,022 − two stubs at 9 each).