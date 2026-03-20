# Migration Notes: Original Library → rocq-domain-theory

This document records, file by file and concept by concept, every
significant change made in modernizing the original pre-migration Coq
library to Rocq 9.0 using the Hierarchy Builder (HB) packed-class
framework. It is intended as a reference for understanding diffs, for
the thesis chapter on formalization methodology, and for anyone porting
proofs written against the old API.

---

## Summary of Major Modernizations

| Theme | Old approach | New approach |
|-------|-------------|--------------|
| Structuring | `Module` system + `Record` | HB mixins + structures |
| Namespace | `From phase0_foundations Require Import` | `From DomainTheory.Structures Require Import` |
| `preorder` | Monolithic `Record preorder` | `HasLe` + `IsPreorder` → `Preorder` |
| `cpo` | Monolithic `Record cpo` with `cpo_pre` field | `HasSup` + `IsCPO` → `CPO` (requires `PartialOrder`) |
| `Pointed` | Separate re-export shim file | Folded into `CPO.v` |
| `Continuous` | Separate module file | `continuous` predicate in `CPO.v`; `cont_fun` in `Morphisms.v` |
| Unproved lubs | `Axiom` in `FunctionSpaces.v`, `Lift.v`, `Sums.v` | All axioms eliminated; lubs proved in `theory/` |
| `Predomains` | Module aliasing `cpo` as `predomain` | Dropped; `CPO` vs `PointedCPO` split handles this |
| `RecursiveDomains` | Empty file | Replaced by `theory/DomainEquations.v` |
| Field names | `le`, `carrier`, `cpo_pre`, `cf_mfun` | `leT`, HB sort coercions, `cf_mono` |
| `proof_irrelevance` | Imported explicitly for `cont_comp_assoc` | Migrated from `Coq.Logic` to `Stdlib.Logic`; still used |
| CPO base | Built on `Preorder` only | Built on `PartialOrder` (follows A&J Definition 2.1.13) |
| `Lift.v` | Axiomatic lubs over `option D` | Classical sup over `option D` using `ClassicalEpsilon` |

---

## File-by-File Migration

---

### `Order.v`

**Old structure:** A single `Record preorder` with fields `carrier`,
`le`, `le_refl`, `le_trans`, all explicit. A partial order was not
separately defined — `le_antisym` appeared wherever needed ad hoc.
`mono_fun` and `chain` were plain records parameterized over `preorder`.

**New structure:** HB hierarchy with three mixins:
```
HasLe → IsPreorder → Preorder
              └── IsPartialOrder → PartialOrder
```

**Specific changes:**

| Old | New | Notes |
|-----|-----|-------|
| `Record preorder` with `carrier` field | `HasLe` mixin; `Preorder.type` sort used as carrier | HB coercions replace explicit `.carrier` projections |
| `Order.le` (field on record) | `leT` (HB field, `T`-suffixed per MathComp convention) | Avoids collision with `Nat.le` in stdlib |
| `x ⊑ y` notation at level 70 | Unchanged | |
| No partial order type | `IsPartialOrder` mixin → `PartialOrder.type` | `le_antisym` now a named field |
| `Order.ch pre c n` (explicit preorder arg) | `c.[n]` (implicit, `ch` field of `chain`) | Simpler; `c.[n]` notation kept |
| `map_chain pre Q f c` (explicit args) | `map_chain f c` (implicit) | Less noise in proofs |
| `Build_mono_fun P Q f mono_pf` (explicit) | `Build_mono_fun f mono_pf` (implicit `{P Q}`) | |
| `pequiv` defined as `x ⊑ y ∧ y ⊑ x` | Preserved as `x ≈ y` | Used in `OrderTheory.v` for setoid reasoning |
| `const_chain`, `tail_chain` | Preserved | Unchanged |
| `mono_comp_assoc` by `reflexivity` | Preserved | Definitional equality still holds |

**What was dropped:** Nothing from `Order.v` was dropped. The content
was reorganized but all definitions survive.

---

### `CPO.v`

**Old structure:** A single `Module Cpo` containing `Record cpo` with
fields `cpo_pre : preorder`, `lub_of_chain`, `lub_upper`, `lub_least`.
Pointed CPOs used `Class Pointed` (typeclass, not a mixin).
`continuous` was defined in a separate `Continuous.v` module.

**New structure:** HB hierarchy:
```
HasSup + PartialOrder → IsCPO → CPO
HasBot + CPO → IsPointed → PointedCPO
```

Note the dependency: `IsPointed` requires `CPO T & HasBottom T`, so
`HasBottom` and `IsPointed` instances must be registered *after* the
`IsCPO` instance. This ordering constraint was the source of an early
bug in `Lift.v` (see `Lift.v` entry below).

**Specific changes:**

| Old | New | Notes |
|-----|-----|-------|
| `Cpo.cpo` with `cpo_pre` field | `CPO.type` with HB sort coercion | No more `.cpo_pre` — use the type directly |
| `Cpo.lub_of_chain D c` | `sup c` (notation `⊔ c`) | Cleaner; `sup` is the HB field |
| `Cpo.lub_upper` / `Cpo.lub_least` | `sup_upper` / `sup_least` | Field names simplified |
| `IsCPO` required only `HasSup & Preorder` | `IsCPO` requires `HasSup & PartialOrder` | **Key semantic change** — see below |
| `Class Pointed(D : cpo) := { ⊥ : D; Pleast : ... }` (typeclass) | `HasBottom` mixin + `IsPointed` mixin → `PointedCPO` | HB over typeclass; no instance search surprises |
| `HasBottom` / `bottom` | `HasBottom` / `bottom` | Name preserved; now an HB mixin instead of part of a typeclass |
| `continuous` in `Continuous.v` | `continuous` predicate in `CPO.v` | Consolidation; avoids separate module import |
| `sup_mono`, `sup_ext` as lemmas in `CPO.v` | Moved to `theory/CPOTheory.v` | Structures file should have no proofs |

**Key semantic change — base of `IsCPO`:**

The old code built `IsCPO` on top of `Preorder` only, with a comment:
> "we do not require a partial order here. A CPO on a preorder is standard."

The new code builds `IsCPO` on `PartialOrder`. This follows Abramsky &
Jung Definition 2.1.13 more faithfully — they define a CPO as a *poset*
in which every directed set has a supremum. More practically, `sup_ext`
(if two chains have pointwise equal elements then their sups are equal)
requires `le_antisym` to prove. The old code had a `TODO` comment noting
this tension:
```coq
(* TODO: Prove without [le_antisym] and revert the definition of [CPO]
         and [IsCPO] to only rely on [Preorder] *)
apply le_antisym; ...
```
Rather than carry this awkwardness, we require `PartialOrder` upfront.

---

### `Continuous.v` → merged into `CPO.v` and `Morphisms.v`

**Old structure:** A separate `Module Continuous` in its own file,
containing `continuous` as a predicate and `cont_fun` as a record with
fields `cf_mfun` and `cf_cont`.

**New structure:** `continuous` is defined as a predicate in `CPO.v`.
`cont_fun` (with `cf_mono` / `cf_cont`) lives in `Morphisms.v`.

| Old | New | Notes |
|-----|-----|-------|
| `Continuous.continuous D E f` (explicit D, E) | `continuous f` (implicit CPO args) | |
| `cf_mfun` field | `cf_mono` | Renamed: it's a `mono_fun`, not a raw function |
| `Continuous.cont_fun D E` | `cont_fun D E` (no module prefix) | |
| `map_chain_id` in `Continuous.v` | In `theory/CPOTheory.v` | Moved to theory layer |
| `id_continuous` in `Continuous.v` | `continuous_id` in `Morphisms.v` | Renamed; same proof |

---

### `Morphisms.v`

**Old structure:** Already partially migrated — had HB imports and the
new-style `cont_fun`/`strict_fun` records. But also imported
`Coq.Logic.ProofIrrelevance` and used it in `cont_comp_assoc`.

**New structure:** Same records, migrated to Rocq 9.0 Stdlib.

| Old | New | Notes |
|-----|-----|-------|
| `Require Import Coq.Logic.ProofIrrelevance` | `From Stdlib Require Import Logic.ProofIrrelevance` | Namespace migrated from `Coq` to `Stdlib`; still used |
| `cont_comp_assoc` via `proof_irrelevance` | Still via `proof_irrelevance` | `apply proof_irrelevance` at two call sites |
| `g ∘ f` notation for `cont_comp` | `Notation "g ∘ f" := (cont_comp g f)` | Preserved in `Morphisms.v`; `⊚` additionally used in `Enriched.v` |
| `strict_comp_strict` (lemma) + `strict_comp` (definition) | `strict_comp` (lemma) + renamed definition | Two names for one concept was confusing |
| `From phase0_foundations Require Import` | `From DomainTheory.Structures Require Import` | Namespace change; capital S matches dune library name |

---

### `Pointed.v`

**Old:** A 12-line re-export shim:
```coq
Module Pointed.
  Definition Pointed := Cpo.Pointed.
  Notation "⊥" := (@Cpo.bottom _ _).
End Pointed.
```

**New:** File not created. `HasBottom` + `IsPointed` + `PointedCPO` live
in `CPO.v`. `strict_fun` lives in `Morphisms.v`. See
`docs/design-decisions.md § DD-001`.

---

### `Predomains.v`

**Old:** A module aliasing `cpo` as `predomain`.

**New:** File not created. The distinction between "predomain" (a CPO
without a required bottom element) and "pointed CPO" is expressed
directly through the HB hierarchy: `CPO.type` is a predomain;
`PointedCPO.type` is a pointed CPO. See `migration-notes.md § Summary`.

---

### `Products.v`

**Old:** A `Module Products` with a monolithic inline construction of
`prod_cpo`. The product preorder, monotone projections, and lubs were
all defined in one large term-mode expression. Correct but unreadable.

**New:** Proof-mode construction in `theory/Products.v` (533 lines),
building up lemmas step by step: `prod_le_refl`, `prod_le_trans`,
`prod_le_antisym`, `prod_sup_upper`, `prod_sup_least`. Then HB instances
assemble the structure. The result is the same but each step is
independently checkable and citeable in the thesis. Also includes:
continuous projections `π₁`/`π₂`, continuous pairing `cont_pair`,
`cont_prod_map`, `cont_swap`, and the universal property.

---

### `Sums.v`

**Old:** Axiomatic lubs:
```coq
Axiom sum_lub_of_chain : forall (A B : Cpo.cpo), chain (sum_pre A B) -> sum_carrier A B.
Axiom sum_lub_upper : ...
Axiom sum_lub_least : ...
```

**New:** All axioms eliminated in `theory/Sums.v` (624 lines). The key
insight is that a chain in `A + B` (separated sum) is eventually entirely
in `inl` or entirely in `inr`, since the orderings do not mix constructors.
The sup is the sup of the eventually-stable projection into `A` or `B`.
This proof is constructive — no classical axioms needed. Note: `A + B` is
deliberately NOT made a `PointedCPO` even when both `A` and `B` are
pointed; the separated sum has no global minimum (`inl ⊥` and `inr ⊥`
are incomparable). For a pointed sum, use `(A + B)⊥`.

---

### `FunctionSpaces.v`

**Old:** Axiomatic lubs for the function-space CPO:
```coq
Axiom fun_cpo_lub : ...
Axiom fun_cpo_lub_upper : ...
Axiom fun_cpo_lub_least : ...
```
The pointwise order was correctly defined but the sup was left as an
axiom. The `fun_cpo` definition was therefore built on unproved axioms
and could not be trusted.

**New:** All axioms eliminated. The pointwise sup of a chain of
continuous functions `c : chain (D ⇒ E)` is defined as
`λ x. sup (map_chain (λ f. f x) c)`, and continuity of this pointwise
sup is proved in `theory/FunctionSpaces.v` (878 lines). This requires:
1. That the family `λ f. f x` is monotone in `f` for fixed `x`.
2. That the pointwise sup of continuous functions is continuous (the key
   lemma, using Scott-continuity of each `f` in the chain and the
   commutativity of the double sup `⊔_n ⊔_m = ⊔_m ⊔_n`).

Reference: Benton-Kennedy §2.1.

---

### `Lift.v`

**Old:** Axiomatic lubs:
```coq
Axiom lift_lub_of_chain : forall (D : Cpo.cpo), chain (lift_pre D) -> lift_carrier D.
Axiom lift_lub_upper : ...
Axiom lift_lub_least : ...
```
The lift was `option D` with `None` as bottom. The `ret` and `kleisli`
were not proved continuous.

**New:** `theory/Lift.v` (646 lines). All axioms eliminated. The carrier
remains `option D` — the *flat* lift — but the sup is now constructed
using `ClassicalEpsilon`:

- `excluded_middle_informative` decides whether the chain ever reaches
  `Some` (not constructively decidable in general).
- `constructive_indefinite_description` extracts a witness index `N`.
- The `D_chain` auxiliary extracts a proper `chain D` from the tail
  `k ↦ c.[N + k]`, using `chain_some_stable` to show the `None` case
  is unreachable.

This uses `ClassicalEpsilon`, which strictly extends the `Classical`
axiom already present in the library. It is the only place outside
`ScottTopology.v` where a classical principle beyond `Classical.v` is
used.

**HB instance ordering fix:** `IsPointed` has the HB dependency
`of CPO T & HasBottom T`. The initial draft registered `HasBottom` and
`IsPointed` before `IsCPO`, which fails. The correct order is:
```
lift_IsCPO → lift_HasBottom → lift_IsPointed
```
This ordering constraint is now documented in `CPO.v` and here.

**Monad structure:** `ret` and `kleisli` are proved Scott-continuous.
The three monad laws (left unit, right unit, associativity) are proved
as propositional equalities using `cont_fun_ext`.

**Supplementary file:** `theory/LiftMonad.v` (488 lines) develops the
coinductive `delay` monad — the alternative to the flat lift — and
proves precisely why it cannot be made into a `CPO.type` without
quotient types. See `design-decisions.md § DD-006` and `§ DD-007`.

Reference: A&J §2.1.4; Moggi (1991); Benton-Kennedy §2.2.

---

### `FixedPoints.v`

**Old:** Effectively empty — just re-exported `Cpo` and declared a
useless `Ltac done := trivial`.

**New:** `theory/FixedPoints.v` (525 lines). Full Kleene fixed-point
theorem:
- `iter f n`: the n-th iterate `fⁿ(⊥)`
- `kleene_chain f`: the chain `⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ ...`
- `fixp f := ⊔ (kleene_chain f)`: the least fixed point
- `fixp_is_fixedpoint`: `f (fixp f) = fixp f`
- `fixp_least`: `fixp f` is the least pre-fixed point
- `fixp_ind`: fixed-point induction for Scott-admissible predicates

The internalized operator `FIXP : (D ⇒c D) →c D` (continuous in `f`)
is deferred to `FunctionSpaces.v` where the function-space CPO is
available.

---

### `RecursiveDomains.v`

**Old:** Completely empty file.

**New:** Replaced by `theory/DomainEquations.v` (446 lines), which
contains the full mixed-variance locally continuous bifunctor framework
and bilimit construction following Benton-Kennedy §4 and A&J §5.2–5.3.

Contents:
- §1: `IsMixedLocallyContinuous` HB mixin with 6 axiom fields (identity,
  composition, separate monotonicity, separate continuity) and
  `MixedLCFunctor` HB structure.
- §2: Packaged `cont_fun` accessors (`MF_mor_l_cont_fun`,
  `MF_mor_r_cont_fun`) and equational rewrites.
- §3: Derived properties — joint monotonicity (`MF_mor_mono`), diagonal
  chain (`mf_diag_chain`), `MF_mor_joint_sup` theorem.
- §4: EP-pair lifting (`mf_ep_pair`) — A&J Proposition 5.2.6: given
  `ep_pair A B`, construct `ep_pair (MF_obj A A) (MF_obj B B)`.
- §5: Approximation sequence (`mf_approx_obj`, `mf_approx_ep`,
  `mf_approx_epc`).
- §6: `BilimitData` record specifying the cone, compatibility, and
  roll/unroll isomorphism. `Axiom bilimit_exists` (requires omega-product
  CPO not yet constructed).
- §7: Consequences — `D_inf`, `ROLL`, `UNROLL`, deflation chain,
  `bil_sup_deflations`, `bil_lim_iso`, `bil_cone_ep`.

0 Admitted proofs; 1 `Axiom` (`bilimit_exists`). See DD-017.

---

### `NatTrans.v` (**new**, Phase 1)

**Old:** Not present in the original Benton-Kennedy library.

**New:** `theory/NatTrans.v` (518 lines) develops enriched natural
transformations between locally continuous endofunctors and proves they
form a CPO under pointwise order.

Contents:
- §1: `nat_trans F G` record with components and naturality.
- §2: Identity (`nt_id`), vertical composition (`nt_vcomp`).
- §3: Left/right whiskering (`nt_lwhisker`, `nt_rwhisker`).
- §4: Pointwise order — `nt_le` with reflexivity, transitivity,
  antisymmetry (natural transformations form a partial order).
- §5: Chains and suprema — `nt_chain_component`, `nt_sup`,
  `nt_sup_upper`, `nt_sup_least` (natural transformations form a CPO).
- §6: Interchange law for vertical and horizontal composition.

0 Admitted. Design: uses `lc_functor` plain record (not HB
`LocallyContinuousFunctor`) to avoid universe inconsistencies. See DD-018.

Reference: Kelly (1982) Ch. 1. Mac Lane (1998) Ch. IX.

---

### `Yoneda.v` (**new**, Phase 1)

**Old:** Not present in the original Benton-Kennedy library.

**New:** `instances/Yoneda.v` (443 lines) constructs the representable
functor and proves the enriched Yoneda lemma.

Contents:
- §1: `repr_functor X` — the covariant hom-functor `Hom(X,-)` as an
  `lc_functor` on `CPO.type`.
- §2: Enriched Yoneda lemma — `yoneda_eval` (extract `alpha_X(id_X)`),
  `yoneda_embed` (given `x : F(X)`, define `alpha_A(f) = F(f)(x)`),
  round-trip laws (`yoneda_eval_embed`, `yoneda_embed_eval`).
- §3: Yoneda isomorphism packaged as an `ep_pair`.

0 Admitted. Lives in `instances/` because it depends on the concrete
CPO-enriched category instance from `Function.v`. See DD-019.

Reference: Kelly (1982), Mac Lane (1998).

---

### `FunLift.v` (**new**, Phase 1)

**Old:** Not present in the original Benton-Kennedy library. The old
`RecursiveDomains.v` was an empty file; no concrete functor instance
existed.

**New:** `instances/FunLift.v` (298 lines) provides the concrete
`MixedLCFunctor` instance on `CPO.type`, connecting the abstract bilimit
machinery in `DomainEquations.v` to the concrete domain constructors in
`FunctionSpaces.v` and `Lift.v`.

The bifunctor maps `(A, B) ↦ ⟨[A →c B]⟩⊥` — the flat lift of the
continuous function space. The morphism action `FL_mor f g` maps
`Some h ↦ Some (g ∘ h ∘ f)` and `None ↦ None`.

Contents:
- §1: `lift_map` — functorial action of the lift on morphisms, defined
  as `kleisli (ret ∘ f)`. Identity, composition, monotonicity lemmas.
- §2: `FL_obj`, `FL_sandwich`, `FL_mor` — object and morphism actions of
  the bifunctor, with computation lemmas (`FL_mor_some`, `FL_mor_none`).
- §3: Six property proofs (`FL_mor_id`, `FL_mor_comp`, `FL_mor_mono_l/r`,
  `FL_mor_cont_l/r`). All use the `change` tactic to bypass
  HB-generated coercion chains — see DD-020. The `None` case in
  continuity proofs uses `lift_sup_none` rather than `le_antisym`.
- §4: HB instance registration (`CPO_HasMixedEndo`,
  `CPO_IsMixedLocallyContinuous`), placed after all proofs to avoid
  canonical-structure interference during rewrites.

0 Admitted. 0 Axioms. Lives in `instances/` because it depends on the
concrete CPO-enriched category instance from `Function.v` and on
`DomainEquations.v`.

Reference: A&J §5.2–5.3. Benton-Kennedy §4.

---

### `QuantumStructure.v` (**new**, Phase 2)

**Old:** Not present in the original Benton-Kennedy library.

**New:** `quantum/QuantumStructure.v` (~340 lines). Provides the base
algebraic structures for quantum domain theory: involutive quantales and
quantum posets, following Kornell-Lindenhovius-Mislove (2024).

Contents:
- §1: `desc_chain` — descending ω-chains (dual of `chain` from Order.v),
  needed for convergence conditions in quantum CPOs.
- §2: `HasQuantaleOps` HB mixin — six operations: `q_top`, `q_bot`,
  `q_prod`, `q_adj`, `q_meet`, `q_inf`.
- §3: `IsInvQuantale` HB mixin — 14 axioms in five groups (top/bottom,
  product, adjoint, meet, infimum). `InvQuantale` HB structure.
- §4: Notation — `⊗` for product, `⊓` for meet.
- §5: `q_delta` — Kronecker delta: Q-valued identity relation using
  decidable equality. Lemmas `q_delta_refl`, `q_delta_neq`.
- §6: `qposet` record — Type + Q-valued order + decidable equality +
  reflexivity + transitivity + antisymmetry axioms. Plain record
  parametrized by `Q : InvQuantale.type` (not an HB structure). See DD-022.
- §7: Derived properties — `qp_antitone_l` (left antitonicity of
  `qp_ord`, used by qCPO.v for descending chains).

Design: Demand-driven axiom set — only operations actually used by
downstream files (qCPO.v, qCPOProperties.v) are included. The quantale
builds on `PartialOrder` from `Order.v`. See DD-022.

0 Admitted. 0 Axioms.

Reference: KLM (2024) Definition 2.2.1 (involutive quantale), §2.3
(quantum sets), Definition 2.6.1 (quantum posets). Weaver (2010)
Definition 2.4.

---

### `qCPO.v` (**new**, Phase 2)

**Old:** Not present in the original Benton-Kennedy library.

**New:** `quantum/qCPO.v` (~390 lines). Quantum chains, convergence, the
quantum CPO property, and Scott continuity in the quantum setting.

Contents:
- §1: `qchain` — ascending quantum chain `K : nat → W → X` with record
  and `qchain_ascending` predicate.
- §2: `qord_chain_descending` — ascending K produces descending sequences
  `n ↦ R(K(n,w), x)` in Q. `qord_desc_chain` packages as `desc_chain`.
- §3: `converges` / `converges_eq` — convergence relation (Kₙ ↗ K∞)
  defined as `R(K∞(w), x) = ⋀ₙ R(K(n,w), x)`.
- §4: `converges_iff_eq` — two-sided ⊑ ↔ equality. `converges_upper` /
  `converges_upper_top` — limit is an upper bound. `converges_unique` —
  limit uniqueness (KLM Proposition 3.1.5).
- §5: `is_qcpo` / `QCPOData` — every ascending quantum chain has a limit.
- §6: `qchain_const` / `converges_const` — constant chain converges to itself.
- §7: `q_monotone` — monotonicity w.r.t. quantum orders.
- §8: `map_qchain` — monotone F applied to a chain yields a chain.
- §9: `q_scott_continuous` — preserves convergence of quantum chains.
- §10: `is_q_bottom`, `QBottom`, `is_pointed_qcpo` — pointed quantum CPOs.

Design: Parametrized by `Q : InvQuantale.type`, `X : qposet Q`, and
`W : Type` (the probe/atom type). W is kept general rather than
specializing to unit (KLM Proposition 3.2.3 lifts from atomic to general
W, but the general form is free via parametricity). See DD-022.

0 Admitted. 0 Axioms.

Reference: KLM (2024) §3.1 (Definition 3.1.1, convergence), §3.2
(Definition 3.2.1, quantum CPO; Definition 3.2.4, Scott continuity;
Proposition 3.1.5, limit uniqueness).

---

## Axioms: Status in Old vs New Library

The old library accumulated `Axiom` declarations for constructions that
were not yet proved. These are **all eliminated** in the new library.

| Axiom | File | Resolution |
|-------|------|-----------|
| `fun_cpo_lub` | `FunctionSpaces.v` | Proved: `λ x. ⊔_n (c n x)` in `theory/FunctionSpaces.v` |
| `fun_cpo_lub_upper` | `FunctionSpaces.v` | Proved from pointwise order definition |
| `fun_cpo_lub_least` | `FunctionSpaces.v` | Proved from `sup_least` applied pointwise |
| `lift_lub_of_chain` | `Lift.v` | Proved via `ClassicalEpsilon` in `theory/Lift.v` |
| `lift_lub_upper` | `Lift.v` | Proved from `D_chain` construction + `le_sup_of_le_elem` |
| `lift_lub_least` | `Lift.v` | Proved from `sup_least` on the extracted `D_chain` |
| `sum_lub_of_chain` | `Sums.v` | Proved constructively using chain stability in `theory/Sums.v` |
| `sum_lub_upper` | `Sums.v` | Follows from above |
| `sum_lub_least` | `Sums.v` | Follows from above |

**Admitted results:** `theory/LiftMonad.v` contains two admitted lemmas
(`bisim_trans` and `converges_bisim`) due to known guardedness-checker
limitations in plain Rocq. These are in the supplementary coinductive
file only; the main library (`Lift.v`) has no admits. See
`design-decisions.md § DD-007`.

**New axiom:** `theory/DomainEquations.v` introduces one `Axiom`
(`bilimit_exists`) asserting the existence of the bilimit of an
approximation sequence. Its proof requires an omega-product CPO
construction not yet in the library. All consequences of the bilimit
are fully proved from the axiom's `BilimitData` record. See
`design-decisions.md § DD-017`.

---

## API Renaming Reference

### Types and Structures

| Old | New |
|-----|-----|
| `Order.preorder` | `Preorder.type` |
| `Cpo.cpo` | `CPO.type` |
| `Cpo.Pointed D` | `PointedCPO.type` |
| `Continuous.cont_fun D E` | `cont_fun D E` |
| `Order.mono_fun P Q` | `mono_fun P Q` |
| `strict_fun D E` | `strict_fun D E` (unchanged) |

### Fields and Projections

| Old | New |
|-----|-----|
| `Order.carrier P` | `P` (HB sort coercion) |
| `Order.le P x y` | `x ⊑ y` |
| `Order.le_refl P x` | `le_refl x` |
| `Order.le_trans P x y z h1 h2` | `le_trans h1 h2` |
| `Cpo.cpo_pre D` | `D` (coercion; `CPO.type` is a `PartialOrder.type`) |
| `Cpo.lub_of_chain D c` | `sup c` or `⊔ c` |
| `Cpo.lub_upper D c n` | `sup_upper c n` |
| `Cpo.lub_least D c x h` | `sup_least c h` |
| `Order.ch P c n` | `c.[n]` |
| `Order.ch_mono P c m n h` | `ch_mono c h` |
| `Order.mf_fun P Q f x` | `f x` (coercion) |
| `Order.mf_mono P Q f x y h` | `mf_mono f h` |
| `Continuous.cf_mfun D E f` | `cf_mono f` |
| `Continuous.cf_cont D E f` | `cf_cont f` |

### Module Imports

| Old | New |
|-----|-----|
| `From phase0_foundations Require Import Order` | `From DomainTheory.Structures Require Import Order` |
| `From phase0_foundations Require Import CPO` | `From DomainTheory.Structures Require Import CPO` |
| `From phase0_foundations Require Import CPO Continuous` | `From DomainTheory.Structures Require Import CPO Morphisms` |
| `Import Order Cpo` | Not needed; HB coercions handle namespacing |

---

### `FunctionSpaces.v` (update: FIXP)

The original FunctionSpaces.v migration (described above) eliminated
axiomatic lubs for the function-space CPO. Since then, §6 (FIXP) has
been added (878 lines total, up from 719):

**Addition:** The `FIXP` operator — `fixp` packaged as a Scott-continuous
map `[[D →c D] →c D]` — now lives in `FunctionSpaces.v` rather than
being deferred. The continuity proof uses a diagonal argument showing
that `⊔_n fixp(f_n)` is a pre-fixed-point of `⊔_n f_n`, then
`fixp_least` gives the ⊑ direction. Bridge lemmas (`fun_sup_app_le`,
`cf_app_sup_le`) handle HB coercion issues between `PointedCPO.type`
and `CPO.type`.

This corresponds to Benton-Kennedy's `FIXP : (D ⇒c D) →c D` from §2.1.

---

### `Function.v` (instances)

**Old:** Not present in the original library. The function-space CPO
instances were registered inline in `FunctionSpaces.v`.

**New:** `instances/Function.v` (462 lines) registers `CPO.type` as a
CPO-enriched category using the enriched category structures from
`Enriched.v`:

| Name | Kind | Description |
|------|------|-------------|
| `CPO_HasHom` | HB instance | `hom A B := cont_fun A B` (using `fun_cpo`) |
| `CPO_HasId` | HB instance | `id_mor := cont_id` |
| `CPO_IsCPOEnriched` | HB instance | `comp := cont_comp`; continuity from `FunctionSpaces.v` |
| `cont_postcomp g` | Definition | `f ↦ g ∘ f` as a continuous map |
| `cont_precomp f` | Definition | `g ↦ g ∘ f` as a continuous map |
| `cont_const` / `cont_K` | Definitions | constant function combinator |
| `cont_ap` | Definition | application at a point |
| `cont_flip` | Definition | flip argument order |

This is the concrete instance of the abstract enriched category framework.
The original Benton-Kennedy library achieved self-enrichment implicitly
through the function-space CPO; our code makes it explicit via HB
instances.

---

### `PCF_Syntax.v`

**Old (Benton-Kennedy §3):** The paper describes the final syntax,
which our implementation follows closely. Benton-Kennedy's constructors
were prefixed with `T` (for "typed"):

```coq
(* Benton-Kennedy 2009, Section 3 — final design *)
Inductive Value : Env → Ty → Type :=
  | TINT : ∀ Γ, nat → Value Γ Int
  | TBOOL : ∀ Γ, bool → Value Γ Bool
  | TVAR : ∀ Γ τ, Var Γ τ → Value Γ τ
  | TFIX : ∀ Γ τ1 τ2, Exp (τ1 :: τ1 -> τ2 :: Γ) τ2 → Value Γ (τ1 -> τ2)
  | TPAIR : ∀ Γ τ1 τ2, Value Γ τ1 → Value Γ τ2 → Value Γ (τ1 * τ2)
with Exp : ...
```

**New (rocq-domain-theory):**

| Old (Benton-Kennedy) | New | Notes |
|----------------------|----|-------|
| `Ty := Int \| Bool \| Arrow \| Prod` | `Ty := Nat \| Bool \| Arrow \| Prod` | `Int` → `Nat` (values are `nat`, not `Z`) |
| `Arrow` notation `->` | `Arrow` notation `→ₜ` | Subscript avoids clash with Rocq function type |
| `Prod` notation `*` | `Prod` notation `×ₜ` | Subscript avoids clash with Rocq product |
| `TINT n` | `NLIT n` | Dropped `T` prefix; `NLIT` for "nat literal" |
| `TBOOL b` | `BLIT b` | `BLIT` for "bool literal" |
| `TVAR i` | `VAR v` | |
| `TFIX e` | `FIX τ₁ τ₂ body` | Explicit type indices in constructor |
| `TPAIR v1 v2` | `PAIR v1 v2` | |
| `TVAL v` | `VAL v` | |
| `TLET e1 e2` | `LET e1 e2` | |
| `TAPP f v` | `APP f v` | |
| `TFST/TSND v` | `FST/SND v` | |
| `TOP op v1 v2` | `OP op v1 v2` | |
| `TGT v1 v2` | `GT v1 v2` | |
| `TIF b e1 e2` | `IFB b e1 e2` | |
| `CExp τ := Exp nil τ` | `CExp τ := Exp [] τ` | `nil` → `[]` |
| `Subst Γ Γ' := ∀ τ, Var Γ τ → Value Γ' τ` | Same | Unchanged |
| `hdSubst` / `tlSubst` | Not used | Substitutions defined differently |
| `substVal` / `substExp` | `substVal` / `substExp` | Same names |
| `singleSubst v` / `doubleSubst v1 v2` | `single_subst v` / `double_subst varg vfun` | Snake_case |

**Structural preservation:** The overall design (intrinsic typing, ANF,
typed de Bruijn indices, renaming-bootstrapped substitution) is exactly
Benton-Kennedy's final approach. The changes are purely cosmetic naming.

**What was dropped:** Benton-Kennedy mention an earlier extrinsic attempt
with raw `nat` indices and a separate `VTy`/`ETy` typing judgment,
which required proving typing uniqueness. This was already abandoned in
their paper; we never implemented it.

---

### `PCF_Operational.v`

**Old (Benton-Kennedy §3):**

```coq
(* Benton-Kennedy 2009, Section 3 *)
Inductive Ev : ∀ τ, CExp τ → CValue τ → Prop :=
  | e_Val : ∀ τ (v : CValue τ), TVAL v ⇓ v
  | e_Op : ∀ op n1 n2, TOP op (TINT n1) (TINT n2) ⇓ TINT (op n1 n2)
  | e_Gt : ∀ n1 n2, TGT (TINT n1) (TINT n2) ⇓ TBOOL (ble_nat n2 n1)
  | e_Fst : ∀ τ1 τ2 (v1 : CValue τ1) (v2 : CValue τ2), TFST (TPAIR v1 v2) ⇓ v1
  | e_Snd : ∀ τ1 τ2 (v1 : CValue τ1) (v2 : CValue τ2), TSND (TPAIR v1 v2) ⇓ v2
  | e_App : ∀ τ1 τ2 e (v1 : CValue τ1) (v2 : CValue τ2),
      substExp (doubleSubst v1 (TFIX e)) e ⇓ v2 → TAPP (TFIX e) v1 ⇓ v2
  | e_Let : ...
  | e_IfTrue : ...
  | e_IfFalse : ...
```

**New (rocq-domain-theory):**

| Old (Benton-Kennedy) | New | Notes |
|----------------------|----|-------|
| `Ev : ∀ τ, CExp τ → CValue τ → Prop` | `Eval : ∀ {τ}, CExp τ → CValue τ → Prop` | Renamed; implicit `τ` |
| `e ⇓ v` := `Ev e v` | `e ⇓ v` := `Eval e v` | Same notation |
| `Converges` not defined | `Converges e := ∃ v, Eval e v` | Added existential wrapper + `e ⇓` notation |
| No determinism proof | `eval_deterministic` | Added: `e ⇓ v₁ → e ⇓ v₂ → v₁ = v₂` |
| No inversion lemmas | `eval_let_inv`, `eval_app_fix_inv`, `eval_ifb_inv` | Added for proof convenience |
| `ble_nat n2 n1` | `n₂ <? n₁` (`Nat.ltb`) | Stdlib modernization |
| `e_App` destructures `TFIX e` directly | `e_App` takes `vf = FIX τ₁ τ₂ body` as premise | More explicit pattern match |

**Structural preservation:** The evaluation rules are the same 9
constructors as Benton-Kennedy (e_Val, e_Op, e_Gt, e_Fst, e_Snd, e_App,
e_Let, e_IfTrue, e_IfFalse). The order and structure of rules are
preserved. The additions (determinism, inversion lemmas) are new utility
results not in the original library.

**What was added:**
- `eval_deterministic`: proves the evaluation relation is functional,
  using `dependent destruction` from `Program.Equality`
- Three inversion lemmas for `LET`, `APP`+`FIX`, and `IFB` expressions
- `Converges` definition with `e ⇓` notation

---

### `PCF_Denotational.v`

**Old (Benton-Kennedy §3.1):**

```coq
(* Benton-Kennedy 2009, Section 3.1 *)
Fixpoint SemExp Γ τ (e : Exp Γ τ) : SemEnv Γ →c (SemTy τ)⊥ :=
  match e with
  | TOP op v1 v2 ⇒ η ∘ uncurry (SimpleOp2 op) ∘ ⟨SemVal v1, SemVal v2⟩
  | TGT v1 v2 ⇒ η ∘ uncurry (SimpleOp2 ble_nat) ∘ ⟨SemVal v2, SemVal v1⟩
  | TAPP v1 v2 ⇒ ev ∘ ⟨SemVal v1, SemVal v2⟩
  | TVAL v ⇒ η ∘ SemVal v
  | TLET e1 e2 ⇒ Kleislir (SemExp e2) ∘ ⟨ID, SemExp e1⟩
  | TIF v e1 e2 ⇒ (choose @3 (SemExp e1)) (SemExp e2) (SemVal v)
  | TFST v ⇒ η ∘ π1 ∘ SemVal v
  | TSND v ⇒ η ∘ π2 ∘ SemVal v
  end with SemVal Γ τ (v : Value Γ τ) : SemEnv Γ →c SemTy τ := ...
```

Benton-Kennedy's substitution lemma:
```coq
Lemma SemCommutesWithSubst:
  (∀ Γ τ (v : Value Γ τ) Γ' (s : Subst Γ Γ'),
    SemVal v ∘ SemSubst s == SemVal (substVal s v))
  ∧ (∀ Γ τ (e : Exp Γ τ) Γ' (s : Subst Γ Γ'),
    SemExp e ∘ SemSubst s == SemExp (substExp s e)).
```

**New (rocq-domain-theory):**

| Old (Benton-Kennedy) | New | Notes |
|----------------------|----|-------|
| `SemTy τ` | `sem_ty τ` | snake_case |
| `SemEnv Γ` | `sem_env Γ` | snake_case |
| `SemVar i` | `sem_var x` | |
| `SemVal v` / `SemExp e` | `sem_val v` / `sem_exp e` | |
| `SemSubst s` | `sem_subst σ` | |
| `SemCommutesWithSubst` | `sem_val_subst` + `sem_exp_subst` | Two separate mutually proved lemmas |
| `SimpleOp2 op` | `nat_binop op` | More descriptive name |
| `uncurry (SimpleOp2 ble_nat)` | `nat_ltb_pair` | Dedicated combinator; `Nat.ltb` replaces `ble_nat` |
| `choose @3 (SemExp e1) (SemExp e2) (SemVal v)` | `cont_ifb ∘ ⟨sem_val v, ⟨sem_exp e₁, sem_exp e₂⟩⟩` | Explicit pairing rather than curried `choose` |
| `Kleislir (SemExp e2) ∘ ⟨ID, SemExp e1⟩` | `kleislir(sem_exp e₂ ∘ swap) ∘ ⟨id, sem_exp e₁⟩` | Uses `cont_swap` for argument reordering |
| `FIXP ∘ curry (curry (SemExp e))` | `FIXP ∘ flip(curry(flip(curry(sem_exp body))))` | Double flip to match binding order |
| `K (n : Discrete nat)` | `cont_const n` | |
| `(SemTy τ)⊥` (coinductive lift) | `option (sem_ty τ)` (flat lift) | See DD-006 |
| `==` (setoid equality) | `=` (Leibniz equality) | See DD-004 |

**Structural preservation:** The overall point-free style of the denotational
semantics is preserved from Benton-Kennedy. Each syntactic case is a
composition of library combinators, producing a `cont_fun` directly.

**What was changed architecturally:**

- **Lift monad:** Benton-Kennedy use a coinductive `Stream` (§2.2) with
  `Eps`/`Val` constructors and a coinductively defined order, requiring
  delicate constructive reasoning for the sup. We use `option D` (flat
  lift) with `ClassicalEpsilon` (see DD-006). This simplifies the monad
  structure and eliminates the quotient problem.

- **Renaming route:** Benton-Kennedy's paper mentions that the substitution
  lemma commutes semantic meaning with syntactic substitution but does not
  detail the proof strategy. Our proof proceeds via an explicit renaming
  route (see DD-012): `sem_ren_ext` → `sem_val_ren`/`sem_exp_ren` →
  `sem_ren_wk` → `sem_val_wk` → `sem_subst_ext` → `sem_val_subst`/`sem_exp_subst`.

- **`var_case` combinator:** The `ren_ext` and `subst_ext` operations use
  a `var_case` combinator (see DD-013) that eliminates `JMeq_eq` opacity.
  This ensures that `sem_ren_ext` and `sem_subst_ext` reduce via kernel
  conversion.

**What was added (not in Benton-Kennedy):**

- `sem_arrow_pointed`: Named definition for the function-type interpretation
  as a `PointedCPO.type`, used to instantiate `FIXP` in the FIX case
- `kleislir`: Parameterised Kleisli extension (Benton-Kennedy's `Kleislir`
  is similar but defined differently; ours has a full standalone continuity
  proof)
- `cont_ifb`: Continuous conditional combinator (replaces Benton-Kennedy's
  `choose`)
- Computation lemmas: `sem_val_NLIT`, `sem_val_BLIT`, `sem_val_PAIR`,
  `sem_val_FIX_unfold`, `sem_exp_VAL`, `sem_exp_LET`, `sem_exp_APP`,
  `sem_exp_FST`, `sem_exp_SND`, `sem_exp_OP`, `sem_exp_GT`, `sem_exp_IFB`,
  `sem_exp_IFB_true`, `sem_exp_IFB_false`
- `⟦v⟧ᵥ`, `⟦e⟧ₑ`, `⟦v⟧ᶜᵥ`, `⟦e⟧ᶜₑ` notation for denotation functions
- `sem_subst_single`, `sem_subst_double`: corollaries connecting the
  single/double substitution combinators from `PCF_Syntax.v` to semantic
  pairing

**Proof status:** All 1169 lines compile with 0 Admitted lemmas. The full
substitution lemma (`sem_val_subst`/`sem_exp_subst`) is proved by mutual
induction, mirroring the structure of `sem_val_ren`/`sem_exp_ren`.

---

### `PCF_Soundness.v`

**Old (Benton-Kennedy §3.2):**

Benton-Kennedy state the soundness theorem:
```
Theorem Soundness: ∀ τ (e : CExp τ) (v : CValue τ),
  Ev e v → SemExp e == η ∘ SemVal v
```
using setoid equality `==` and stated in a point-free form (as an equality
of continuous functions). The proof is described as an induction on `Ev`.

**New (rocq-domain-theory):**

| Old (Benton-Kennedy) | New | Notes |
|----------------------|----|-------|
| `SemExp e == η ∘ SemVal v` (point-free, setoid) | `sem_exp e tt = Some (sem_val v tt)` (pointwise, Leibniz) | Closed-term form; see DD-004 |
| Stated for open terms with semantic environments | Stated for closed terms only (sufficient for adequacy) | Simpler statement |
| `Ev` as derivation type name | `Eval` (notation `e ⇓ v`) | Renamed |

**Structural preservation:** The proof follows the same strategy as
Benton-Kennedy — structural induction on the evaluation derivation. Each
case uses the computation rules from `PCF_Denotational.v` plus the
induction hypothesis. The LET and APP cases are the non-trivial ones,
requiring the substitution lemmas.

**What was added (not in Benton-Kennedy):**
- `sem_single_subst` / `sem_double_subst`: local interface lemmas
  specializing the substitution lemma at the closed-term level
- `soundness_not_none`: convergence implies non-⊥ denotation
- `soundness_val`: values denote themselves
- `soundness_denotation_agree`: co-evaluating terms have equal denotations

**Proof status:** 261 lines, 0 Admitted.

---

### `PCF_Adequacy.v`

**Old (Benton-Kennedy §3.2):**

Benton-Kennedy state the adequacy theorem:
```
Theorem Adequacy: ∀ τ (e : CExp τ),
  SemExp e ≠ ⊥ → Converges e
```
and describe the proof via a logical relation (type-indexed family of
relations between denotations and syntactic terms). The proof details
are given in the paper but not in the Coq formalization — the original
library left adequacy unproved.

**New (rocq-domain-theory):**

| Old (Benton-Kennedy) | New | Notes |
|----------------------|----|-------|
| Theorem stated but unproved | `adequacy` fully proved (820 lines) | **Key new contribution** |
| `SemExp e ≠ ⊥` | `sem_exp e tt <> None` | `option D` lift; `None` is `⊥` |
| `Converges e` (undefined in original) | `e ⇓` := `∃ v, e ⇓ v` | Uses `Converges` from `PCF_Operational.v` |
| Logical relation described in paper | `rel_val`/`rel_exp` by `Fixpoint` on `Ty` | Fully formalized |

**Structural preservation:** The proof follows the paper's strategy:
define a type-indexed logical relation, prove a fundamental lemma by
mutual induction on syntax, derive adequacy as a corollary for closed
terms at the empty environment.

**What was added (not in Benton-Kennedy formalization):**

- `rel_val` / `rel_exp`: The logical relation, defined as a mutual
  `Fixpoint` on `Ty`. `rel_exp` is the lift of `rel_val` through the
  option monad.
- `rel_val_admissible`: Admissibility of `rel_val` in the denotational
  argument, proved by induction on `Ty`. Uses chain-stabilisation
  properties of the lift CPO and `eval_deterministic` from
  `PCF_Operational.v`.
- `rel_exp_admissible`: Admissibility of `rel_exp`, derived from
  `rel_val_admissible`.
- `rel_exp_admissible_pointwise`: Pointwise variant for the FIX case.
- `rel_env`: Environment relation (semantic environment related to
  syntactic substitution).
- `fundamental_lemma`: The core result — every well-typed term
  instantiated by a related environment lies in the logical relation.
  Proved via `Combined Scheme val_exp_ind` (mutual induction on
  `Value`/`Exp`).
- `convergence_iff_defined`: Full operational/denotational correspondence
  `e ⇓ ↔ sem_exp e tt <> None`, combining `soundness` and `adequacy`.
- `convergence_implies_defined`: The "easy" direction restated for
  convenience.

**Key proof techniques:**
- The FIX case uses `fixp_ind` (Scott's induction principle) with a
  natural-number induction nested inside.
- Admissibility proofs use `lift_sup_some_eq`, `chain_some_stable`,
  `D_chain_fn_eq`, and `eval_deterministic` extensively.
- The arrow case in `rel_val_admissible` extracts the body from
  `FIX τ₁ τ₂ body` using `Eqdep.EqdepTheory.inj_pair2` to invert
  dependent pairs.
- Imports `Classical` for `excluded_middle` in chain case analysis.

**Proof status:** 820 lines, 0 Admitted. The most technically demanding
file in the library.

**Combined correspondence:** Together, `PCF_Soundness.v` and
`PCF_Adequacy.v` establish:
```
e ⇓  ↔  sem_exp e tt <> None
```
This is the crown-jewel result of the PCF development, validating the
entire domain-theory framework.

---

### `EnrichedTheory.v` (**new**, Phase 1)

**Old:** Not present in the original Benton-Kennedy library. The
original code had no notion of CPO-enriched categories, locally
continuous functors, or embedding-projection pairs as abstract concepts.
These were used implicitly (e.g., the self-enrichment of CPO was implicit
in the function-space CPO construction).

**New:** `theory/EnrichedTheory.v` (706 lines) develops the derived
theory for CPO-enriched categories in four sections:

| Section | Key definitions | Lines |
|---------|----------------|-------|
| §1 Continuity equations | `comp_cont_l_eq`, `comp_cont_r_eq`, `F_mor_sup_eq` | ~50 |
| §2 Joint continuity | `comp_chain`, `comp_joint_sup`, `comp_joint_continuous`, `comp_joint_cont_fun`, `comp_joint_apply` | ~155 |
| §3 LC functors | `lc_functor` record, `lc_functor_of_hb`, `id_lc_functor`, `comp_lc_functor` | ~200 |
| §4 EP-pairs | `ep_pair` record, `ep_id`, `ep_comp`, order lemmas, `ep_chain` record | ~260 |

**What was added (not in Benton-Kennedy):**

- **Joint continuity of composition** (§2): Derives the joint Scott-continuity
  of `comp : Hom(B,C) × Hom(A,B) → Hom(A,C)` from the separate continuity
  axioms in `IsCPOEnriched`, using a two-stage proof (product-free core +
  product packaging) to work around HB coercion conflicts. This is A&J
  Lemma 3.2.6 applied to the abstract enriched setting.

- **`lc_functor` plain record** (§3): A record bundling an endofunctor on a
  CPO-enriched category with locally-continuous axioms, separate from the
  HB `LocallyContinuousFunctor` structure. Includes `lc_functor_of_hb` for
  converting HB instances, plus identity and composition constructions.

- **EP-pair infrastructure** (§4): `ep_pair` record with retraction and
  deflation laws, `ep_id`, `ep_comp`, order lemmas (`ep_emb_mono`,
  `ep_proj_mono`, `ep_proj_emb_cancel`), and `ep_chain` record for
  ω-sequences of EP-pairs. This is the foundation for `DomainEquations.v`.

**HB coercion workarounds:** This file required extensive workarounds for
HB canonical structure resolution failures when compiling from source.
See `design-decisions.md § DD-016` for the full list.

**Proof status:** 706 lines, 0 Admitted.

Reference: A&J §5.2. Benton-Kennedy §4. Kelly (1982).

---

## What the Old Library Got Right

The following design choices from the original (and from Benton-Kennedy)
are preserved unchanged:

- **`chain` as a record** (not an HB structure): chains are data, not
  carriers of new algebraic structure.
- **`mono_fun` as a record** with a coercion to the underlying function.
- **Separating `strict_fun` from `cont_fun`**: strictness is not always
  required.
- **`pequiv` (`x ≈ y`)** for preorder-level equivalence.
- **The `c.[n]` notation** for chain access.
- **Diagrammatic argument ordering** in composition (`g ∘ f` meaning
  "first f, then g").