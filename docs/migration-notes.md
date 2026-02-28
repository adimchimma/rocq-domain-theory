# Migration Notes: Original Library → rocq-domain-theory

This document records, file by file and concept by concept, every
significant change made in modernizing the original pre-migration Coq
library to Rocq 9.0 using the Hierarchy Builder (HB) packed-class
framework. It is intended as a reference for understanding diffs, for
the thesis chapter on formalization methodology, and for anyone porting
proofs that were written against the old API.

---

## Summary of Major Modernizations

| Theme | Old approach | New approach |
|-------|-------------|--------------|
| Structuring | `Module` system + `Record` | HB mixins + structures |
| Namespace | `From phase0_foundations Require Import` | `From DomainTheory.structures Require Import` |
| `preorder` | Monolithic `Record preorder` | `HasLe` + `IsPreorder` → `Preorder` |
| `cpo` | Monolithic `Record cpo` with `cpo_pre` field | `HasSup` + `IsCPO` → `CPO` (requires `PartialOrder`) |
| `Pointed` | Separate re-export shim file | Folded into `CPO.v` |
| `Continuous` | Separate module file | `continuous` predicate in `CPO.v`; `cont_fun` in `Morphisms.v` |
| Unproved lubs | `Axiom` in `FunctionSpaces.v`, `Lift.v`, `Sums.v` | All axioms eliminated; lubs proved in `theory/` |
| `Predomains` | Module aliasing `cpo` as `predomain` | Dropped; `CPO` vs `PointedCPO` split handles this |
| `RecursiveDomains` | Empty file | Replaced by `theory/DomainEquations.v` |
| Field names | `le`, `carrier`, `cpo_pre`, `cf_mfun` | `leT`, HB sort coercions, `cf_mono` |
| `proof_irrelevance` | Imported explicitly for `cont_comp_assoc` | Avoided; equality proved structurally |
| CPO base | Built on `Preorder` only | Built on `PartialOrder` (follows A&J Definition 2.1.13) |

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
| `pequiv` defined as `x ⊑ y ∧ y ⊑ x` | Preserved as `x ≈ y` | Will be needed in `OrderTheory.v` for setoid reasoning |
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

**Specific changes:**

| Old | New | Notes |
|-----|-----|-------|
| `Cpo.cpo` with `cpo_pre` field | `CPO.type` with HB sort coercion | No more `.cpo_pre` — use the type directly |
| `Cpo.lub_of_chain D c` | `sup c` (notation `⊔ c`) | Cleaner; `sup` is the HB field |
| `Cpo.lub_upper` / `Cpo.lub_least` | `sup_upper` / `sup_least` | Field names simplified |
| `IsCPO` required only `HasSup & Preorder` | `IsCPO` requires `HasSup & PartialOrder` | **Key semantic change** — see below |
| `Class Pointed(D : cpo) := { ⊥ : D; Pleast : ... }` (typeclass) | `HasBot` mixin + `IsPointed` mixin → `PointedCPO` | HB over typeclass; no instance search surprises |
| `HasBottom` / `bottom` | `HasBot` / `bot` (or `bottom`) | Name shortened |
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
If a genuinely non-antisymmetric CPO is ever needed (e.g. for a
quotient construction), it can be handled as a separate `PreCPO` mixin.

---

### `Continuous.v` → merged into `CPO.v` and `Morphisms.v`

**Old structure:** A separate `Module Continuous` in its own file,
containing `continuous` as a predicate and `cont_fun` as a record with
fields `cf_mfun` and `cf_cont`.

**New structure:** `continuous` is defined as a predicate in `CPO.v`.
`cont_fun` (with `cf_mono` / `cf_cont`) lives in `Morphisms.v`.

**Specific changes:**

| Old | New | Notes |
|-----|-----|-------|
| `Continuous.continuous D E f` (explicit D, E) | `continuous f` (implicit CPO args) | |
| `cf_mfun` field | `cf_mono` | Renamed for clarity: it's a `mono_fun`, not a raw function |
| `Continuous.cont_fun D E` | `cont_fun D E` (no module prefix) | |
| `map_chain_id` in `Continuous.v` | In `theory/CPOTheory.v` | Moved to theory layer |
| `id_continuous` in `Continuous.v` | `continuous_id` in `Morphisms.v` | Renamed; same proof |

---

### `Morphisms.v`

**Old structure:** Already partially migrated in the original — had HB
imports and the new-style `cont_fun`/`strict_fun` records. But also
imported `Coq.Logic.ProofIrrelevance` and used it in `cont_comp_assoc`.

**New structure:** Same records, cleaned up.

**Specific changes:**

| Old | New | Notes |
|-----|-----|-------|
| `Require Import Coq.Logic.ProofIrrelevance` | Removed | See below |
| `cont_comp_assoc` via `proof_irrelevance` | Via structural equality | |
| `g ∘ f` notation for `cont_comp` | Notation dropped from `Morphisms.v` | `⊚` used instead in `Enriched.v` for categorical composition; `∘` reserved for Rocq's stdlib |
| `strict_comp_strict` (lemma) + `strict_comp` (definition) | `strict_comp` (lemma) + renamed definition | Two names for one concept was confusing |
| `From DomainTheory.Structures` (capital S) | `From DomainTheory.structures` (lowercase) | Case fix; dune library names are lowercase |

**On removing `proof_irrelevance`:**

The old `cont_comp_assoc` proof was:
```coq
Lemma cont_comp_assoc ... : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  unfold cont_comp. f_equal. destruct h, g, f.
  apply proof_irrelevance.
Qed.
```
This works but is unsatisfying: it means the proof obligation is
discharged by an axiom (proof irrelevance) rather than by computation.
In the new library, `cont_comp_assoc` follows from `mono_comp_assoc`
(which holds by `reflexivity` since `mono_fun` composition is
definitionally associative) together with `cont_fun_eq` (two continuous
functions are equal if their underlying `mono_fun`s are equal). The
continuity proofs are then equal by `proof_irrelevance` if needed, but
this should be avoidable with careful use of `Prop` irrelevance built
into Rocq's kernel rather than the explicit axiom.

---

### `Pointed.v`

**Old:** A 12-line re-export shim:
```coq
Module Pointed.
  Definition Pointed := Cpo.Pointed.
  Notation "⊥" := (@Cpo.bottom _ _).
End Pointed.
```

**New:** File not created. `HasBot` + `IsPointed` + `PointedCPO` live
in `CPO.v`. `strict_fun` lives in `Morphisms.v`. See
`docs/design-decisions.md § DD-001`.

---

### `Predomains.v`

**Old:** A module aliasing `cpo` as `predomain`:
```coq
Module Predomains.
  Definition predomain := Cpo.cpo.
  Coercion predomain_to_pre (D : predomain) : preorder := Cpo.cpo_pre D.
  Definition mono (D E : predomain) := mono_fun D E.
End Predomains.
```

**New:** File not created. The distinction between "predomain" (a CPO
without a required bottom element) and "pointed CPO" is now expressed
directly through the HB hierarchy: `CPO.type` is a predomain;
`PointedCPO.type` is a pointed CPO. No alias is needed. This follows
Benton-Kennedy's own observation (§2.1) that the main benefit of
predomains over pointed CPOs is exactly that they need not have a bottom
element — which our `CPO`/`PointedCPO` split captures natively.

---

### `Products.v`

**Old:** A `Module Products` with a monolithic inline construction of
`prod_cpo`. The product preorder, monotone projections, and lubs were
all defined in one large term-mode expression. Correct but unreadable:
```coq
Definition prod_cpo (A B : Cpo.cpo) : Cpo.cpo :=
  let pre : Order.preorder := Order.Build_preorder
    (carrier ... * carrier ...)
    (fun p q => (le ... (fst p) (fst q)) /\ ...)
    ...
```

**New:** Proof-mode construction in `theory/Products.v`, building up
lemmas step by step: `prod_le_refl`, `prod_le_trans`, `prod_le_antisym`,
`prod_sup_upper`, `prod_sup_least`. Then `prod_cpo` assembles them. The
result is the same but each step is independently checkable and citeable
in the thesis.

---

### `Sums.v`

**Old:** Axiomatic lubs:
```coq
Axiom sum_lub_of_chain : forall (A B : Cpo.cpo), chain (sum_pre A B) -> sum_carrier A B.
Axiom sum_lub_upper : ...
Axiom sum_lub_least : ...
```

**New:** All axioms eliminated. The key insight is that a chain in
`A ⊕ B` (separated sum) must eventually be entirely in `inl` or
entirely in `inr` (since the orderings do not mix `inl` and `inr`
values). The lub is then the lub of the eventually-constant projection
into `A` or `B`. This proof is non-trivial constructively and belongs in
`theory/Sums.v`.

---

### `FunctionSpaces.v`

**Old:** Axiomatic lubs for the function-space CPO:
```coq
Axiom fun_cpo_lub : forall (D E : Cpo.cpo) (fun_pre : Order.preorder),
  Order.chain fun_pre -> Order.carrier fun_pre.
Axiom fun_cpo_lub_upper : ...
Axiom fun_cpo_lub_least : ...
```
The pointwise order was correctly defined but the sup was left as an
axiom. The `fun_cpo` definition was therefore built on unproved axioms
and could not be trusted.

**New:** All axioms eliminated. The pointwise sup of a chain of
continuous functions `c : chain (D ⇒ E)` is defined as
`λ x. sup (map_chain (λ f. f x) c)`, and continuity of this pointwise
sup is proved in `theory/FunctionSpaces.v`. This requires:
1. That the family `λ f. f x` is monotone in `f` for fixed `x` (from
   the pointwise order definition).
2. That the pointwise sup of continuous functions is continuous (the key
   lemma, which uses Scott-continuity of each `f` in the chain and the
   commutativity of the double sup `⊔_n ⊔_m = ⊔_m ⊔_n`).

Reference: Benton-Kennedy §2.1, "D1 ⇒c D2 : cpo ... if c : natO →m
(D1 →c D2) is a chain, then ⊔c : (D1 →c D2) is λd1. ⊔(λn. c n d1)".

---

### `Lift.v`

**Old:** Axiomatic lubs:
```coq
Axiom lift_lub_of_chain : forall (D : Cpo.cpo), chain (lift_pre D) -> lift_carrier D.
Axiom lift_lub_upper : ...
Axiom lift_lub_least : ...
```
The lift was `option D` with `None` as bottom, which is the *flat* lift
(adding a single new bottom under all existing elements). The `ret` and
`bind` were not proved continuous.

**New:** The flat `option`-based lift is replaced by the coinductive
`Stream`-based constructive lift following Benton-Kennedy §2.2. This is
more complex but:
1. Eliminates the axioms.
2. Makes the lift a genuine monad (not just a pointed CPO with an
   ad-hoc unit).
3. Supports the `kleisli` operator needed for PCF adequacy.

The old `lift_carrier D := option D` approach would suffice for a
classical treatment but fails constructively: determining whether a
chain in `D⊥` converges requires an unbounded search, which is not a
total Rocq function. The `Stream`/corecursive approach handles this.

Reference: Benton-Kennedy §2.2, Capretta (2005) on general recursion
via coinductive types.

---

### `FixedPoints.v`

**Old:** Effectively empty — just re-exported `Cpo` and declared a
useless `Ltac done := trivial`.

**New:** `theory/FixedPoints.v` will contain the full Kleene fixed-point
theorem:
- `kleene_chain`: the chain `⊥, f(⊥), f(f(⊥)), ...`
- `kleene_chain_upper`: each iterate is below the sup
- `fixp f := sup (kleene_chain f)` for `f : D →c D`, `D : PointedCPO`
- `fixp_least`: `fixp` is the least fixed point
- `FIXP : (D ⇒c D) →c D`: the internalized, continuous fixed-point operator
- `fixp_ind`: fixed-point induction for admissible predicates

---

### `RecursiveDomains.v`

**Old:** Completely empty file.

**New:** Replaced by `theory/DomainEquations.v`, which will contain the
full inverse-limit construction following Benton-Kennedy §4 and A&J §5.3.

---

## API Renaming Reference

Quick lookup table for anyone porting old proofs.

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
| `sf_cont f` | `sf_cont f` (unchanged) |
| `sf_strict f` | `sf_strict f` (unchanged) |

### Constructors

| Old | New |
|-----|-----|
| `Order.Build_preorder carrier le refl trans` | `HB.pack` / instance mechanism |
| `Cpo.mk_cpo pre lub upper least` | `HB.pack` / instance mechanism |
| `Build_mono_fun P Q f mono` | `Build_mono_fun f mono` (implicit `{P Q}`) |
| `Build_cont_fun D E mono cont` | `Build_cont_fun mono cont` (implicit `{D E}`) |
| `Build_chain P ch mono` | `Build_chain ch mono` (implicit `{P}`) |

### Lemmas

| Old | New | Location |
|-----|-----|----------|
| `sup_mono` | `sup_mono` | `theory/CPOTheory.v` |
| `sup_ext` | `sup_ext` | `theory/CPOTheory.v` |
| `continuous_id` | `continuous_id` | `Morphisms.v` |
| `continuous_comp` | `continuous_comp` | `Morphisms.v` |
| `cont_comp_assoc` | `cont_comp_assoc` | `Morphisms.v` |
| `cont_comp_id_l/r` | `cont_id_l/r` | `Morphisms.v` |
| `strict_comp_strict` | `strict_comp` (lemma) | `Morphisms.v` |
| `map_chain_id` | `map_chain_id` | `theory/CPOTheory.v` |

### Module Imports

| Old | New |
|-----|-----|
| `From phase0_foundations Require Import Order` | `From DomainTheory.structures Require Import Order` |
| `From phase0_foundations Require Import CPO` | `From DomainTheory.structures Require Import CPO` |
| `From phase0_foundations Require Import CPO Continuous` | `From DomainTheory.structures Require Import CPO Morphisms` |
| `Import Order Cpo` | Not needed; HB coercions handle namespacing |
| `Import Order.` (dot-import) | Not used in new library |

---

## What the Old Library Got Right

Not everything needed changing. The following design choices from the
original (and from Benton-Kennedy) are preserved unchanged:

- **`chain` as a record** (not an HB structure): chains are data, not
  carriers of new algebraic structure. Keeping them as plain records
  avoids over-engineering.
- **`mono_fun` as a record** with a coercion to the underlying function:
  this is the right abstraction level for Phase 0.
- **Separating `strict_fun` from `cont_fun`**: strictness is not always
  required; keeping it separate avoids polluting the continuous function
  API.
- **`pequiv` (x ≈ y)** for preorder-level equivalence: useful for
  setoid rewriting when working with quotient constructions.
- **The `c.[n]` notation** for chain access: clean and unambiguous.
- **Diagrammatic argument ordering** in composition (`g ∘ f` meaning
  "first f, then g"): consistent with categorical convention.

---

## Axioms: Status in Old vs New Library

The old library accumulated several `Axiom` declarations for
constructions that were not yet proved. These are **all eliminated** in
the new library. The table below tracks each one.

| Axiom | File | Resolution |
|-------|------|-----------|
| `fun_cpo_lub` | `FunctionSpaces.v` | Proved: `λ x. ⊔_n (c n x)` in `theory/FunctionSpaces.v` |
| `fun_cpo_lub_upper` | `FunctionSpaces.v` | Proved from pointwise order definition |
| `fun_cpo_lub_least` | `FunctionSpaces.v` | Proved from `sup_least` applied pointwise |
| `lift_lub_of_chain` | `Lift.v` | Replaced by coinductive `Stream` construction |
| `lift_lub_upper` | `Lift.v` | Follows from coinductive definition |
| `lift_lub_least` | `Lift.v` | Follows from coinductive definition |
| `sum_lub_of_chain` | `Sums.v` | Proved using eventual-constancy of chains in `A ⊕ B` |
| `sum_lub_upper` | `Sums.v` | Follows from above |
| `sum_lub_least` | `Sums.v` | Follows from above |

The theorem checker confirms: the final library should compile with
`Print Assumptions` returning only Rocq's built-in axioms (`Classical`,
`FunctionalExtensionality` if used, etc.) and **no** user-declared
`Axiom` or `admit`.