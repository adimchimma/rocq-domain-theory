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

**New:** Replaced by `theory/DomainEquations.v`, which will contain the
full inverse-limit construction following Benton-Kennedy §4 and A&J §5.3.

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