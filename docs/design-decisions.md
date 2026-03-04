# Design Decisions

This document records non-obvious architectural choices made during the
modernization of the Benton-Kennedy domain theory library for Rocq 9.0,
so that future contributors (and the thesis write-up) have context for
why things are the way they are.

---

## DD-001: `Pointed.v` not created as a separate file

**Decision:** `HasBottom`, `IsPointed`, `PointedCPO` live in `CPO.v`.
`strict_fun` lives in `Morphisms.v`. No `Pointed.v` is created.

**Rationale:**

The original pre-migration codebase had a `Pointed.v` that was a
one-line re-export shim:

```coq
(* old Pointed.v *)
Module Pointed.
  Definition Pointed := Cpo.Pointed.
  Notation "⊥" := (@Cpo.bottom _ _).
End Pointed.
```

A re-export shim of this kind is an anti-pattern in MathComp/HB-style
libraries for two reasons:

1. **Indirection without benefit.** A user searching for `IsPointed`
   who follows `Require Import Pointed` lands in a file that immediately
   bounces them to `CPO.v`. The shim adds a conceptual layer without
   adding any definitions, lemmas, or structure.

2. **Silent change propagation.** If `HasBottom` is moved or renamed in
   `CPO.v`, the shim silently changes what it re-exports.

The better practice (following MathComp convention) is to organize files
around dependency structure, not an idealized mental model of separate
concepts. `IsPointed` has a hard dependency on `CPO T` — it belongs in
`CPO.v`. `strict_fun` has a hard dependency on `cont_fun` — it belongs in
`Morphisms.v`. A downstream file that wants both writes:

```coq
From DomainTheory.structures Require Import CPO Morphisms.
```

**Affected files:**
- `src/structures/CPO.v` — contains `HasBottom`, `IsPointed`, `PointedCPO`
- `src/structures/Morphisms.v` — contains `strict`, `strict_fun`
- `src/structures/Pointed.v` — **not created**

---

## DD-002: Separate continuity axioms in `IsCPOEnriched`

**Decision:** `IsCPOEnriched` axiomatises composition via two separate
Scott-continuity conditions (`comp_cont_l` and `comp_cont_r`) rather than
a single joint continuity condition.

**Rationale:**

The natural statement of CPO-enrichment is that composition
`comp : Hom(A,B) × Hom(B,C) → Hom(A,C)` is jointly Scott-continuous.
However, Abramsky & Jung Lemma 3.2.6 states:

> A function f : D × E → F is Scott-continuous if and only if it is
> Scott-continuous in each variable separately.

So the two formulations are equivalent. We choose separate continuity
because the joint form would require importing `Products.v` (for the
product CPO `Hom(A,B) × Hom(B,C)`) at the point where `Enriched.v` is
declared, creating a forward dependency cycle:

```
Enriched.v → Products.v → CPOTheory.v → Enriched.v  (cycle)
```

Using separate continuity breaks the cycle entirely.

This is precisely the strategy used in Kornell-Lindenhovius-Mislove (2024)
§3.3 to prove qCPO is enriched over CPO.

**Affected files:**
- `src/structures/Enriched.v` — `IsCPOEnriched.comp_cont_l/r`
- `src/theory/EnrichedTheory.v` — should derive the joint form once
  `Products.v` is available

---

## DD-003: Monotonicity fields precede continuity fields in HB mixins

**Decision:** In every mixin where both monotonicity and Scott-continuity
are required, the monotonicity field is declared *before* the continuity
field.

**Rationale:**

The `continuous` predicate takes a `mono_fun` as its argument.
`Build_mono_fun` requires a proof of monotonicity. If a continuity field
appears before the monotonicity field in an HB mixin, the proof term
`Build_mono_fun (fun x => ...) comp_mono_l` in the continuity field has
no `comp_mono_l` in scope yet. Placing monotonicity first ensures the
proof compiles.

This is a Rocq-HB implementation detail, not a mathematical preference.

---

## DD-004: Leibniz equality for categorical laws

**Decision:** The categorical laws in `IsCPOEnriched` and
`IsLocallyContinuous` use Leibniz equality `=` rather than setoid
equality `≈`.

**Rationale:**

The hom-CPOs in our framework are HB-packed types (`CPO.type`), and the
equality on their elements is Leibniz equality by default. Using `=` keeps
the categorical laws definitionally true and avoids the overhead of setoid
rewriting infrastructure at the structure level.

If a concrete instance uses a coarser extensional equality (e.g.
`f ≈ g ↔ ∀ x, f x = g x`), the laws should be restated using `≈` in the
relevant theory file. See Benton-Kennedy §2.1, which uses `==` throughout
but notes the tension between pointwise and point-free styles.

---

## DD-005: `HasMixedEndo` records only data; axioms deferred

**Decision:** The mixin `HasMixedEndo` in `Enriched.v` contains only the
object and morphism action of a mixed-variance bifunctor. The functoriality
and local-continuity axioms are deferred to `src/theory/DomainEquations.v`.

**Rationale:**

The full axioms for a mixed-variance locally continuous bifunctor require
reasoning about directed sets of pairs of morphisms, which in turn
requires the product CPO construction. Declaring the axioms in `Enriched.v`
would create the same forward-dependency cycle described in DD-002.

By splitting data (`HasMixedEndo` in `Enriched.v`) from axioms
(`IsMixedLocallyContinuous` in `DomainEquations.v`), the structures file
stays dependency-minimal.

---

## DD-006: `Lift.v` uses `option D` with `ClassicalEpsilon`, not coinduction

**Decision:** The main library lift (`src/theory/Lift.v`) uses the flat
carrier `option D` with a classically-computed sup. A coinductive
alternative is developed in the supplementary file `LiftMonad.v`.

**Rationale:**

The original migration notes suggested replacing the axiomatic lift with
a coinductive `delay D` type following Benton-Kennedy §2.2. This direction
was investigated and found to have a fundamental obstruction:

**The antisymmetry obstruction.** The terms `now d` and `later (now d)`
in the coinductive type `delay D` are propositionally distinct
(`now d ≠ later (now d)` by `discriminate`) but semantically equivalent
(both converge to `d`). Any CPO order that is compatible with convergence
would have `now d ⊑ later (now d)` and `later (now d) ⊑ now d`
simultaneously, and antisymmetry would then force `now d = later (now d)` —
a contradiction.

This means `delay D` cannot be made into a `CPO.type` (which uses Leibniz
equality, as per DD-004) without first quotienting by weak bisimulation.
The quotient construction requires either:
- Setoid-based CPO framework (significant infrastructure change)
- The `Quotient` library or HITs (not standard in Rocq)
- Axioms beyond what the library already uses

The `option D` approach avoids the quotient entirely. Its sup requires
`ClassicalEpsilon` (for `excluded_middle_informative` and
`constructive_indefinite_description`) to decide whether a chain
converges, but this is the only non-constructive step and is localized
to `lift_sup`. The monad structure (`ret`, `kleisli`, all three monad
laws) is proved without further classical principles.

**Axiom audit for `Lift.v`:**
- `ClassicalEpsilon` (via `Stdlib.Logic.ClassicalEpsilon`)
- `Classical` is already a dependency of `ScottTopology.v`; `ClassicalEpsilon`
  strictly extends it and is the only additional axiom

**What `option D` loses vs `delay D`:** The flat lift `option D = D⊥`
correctly models partiality as a *domain-theoretic* effect — adding a
fresh bottom to an existing CPO. It does not directly model *computational
steps* (the number of reduction steps to reach a value). For PCF
adequacy, this is sufficient: the denotation of a program is in `D⊥`,
and whether it equals `Some v` (converging) or `None` (diverging) is all
that matters. The coinductive structure of `delay D` models computation
steps more faithfully but is not needed for the main theorem.

**References:** Capretta (2005), Chapman-Uustalu-Veltri (2019),
Moggi (1991).

---

## DD-007: `LiftMonad.v` as a self-contained supplementary file

**Decision:** The coinductive delay monad is developed in a separate file
`src/theory/LiftMonad.v` that has no imports and is not used by any
other file in the library.

**Rationale:**

The file serves two purposes for the thesis:

1. **Comparison:** By developing the monad structure for `delay D` in
   full (the `bind` corecursion, `bind_now`/`bind_later` computation
   rules using the "frob" trick, and the monad laws up to bisimulation),
   the thesis can compare the `option D` and `delay D` approaches
   concretely side by side.

2. **Obstruction theorem:** The file culminates in
   `delay_CPO_requires_quotient`, which gives a precise Rocq proof of
   the three facts establishing that `delay D` cannot be a `CPO.type`
   without quotient types (Facts A, B, C in §6).

The file is deliberately kept self-contained (no imports) to emphasize
that the coinductive structure is logically independent of the
domain-theory hierarchy.

**Admitted results in `LiftMonad.v`:**

Two lemmas are partially admitted due to known limitations of Rocq's
productivity checker:

- `bisim_trans`: The `bisim_right/bisim_left` case requires a corecursive
  call not under any constructor. The remaining 5 cases are proved.

- `converges_bisim`: The `conv_now/bisim_right` and
  `conv_later/bisim_right` cases require inverting a coinductive
  hypothesis inside an inductive recursion — structurally forbidden.

Both are classically true and provable in Agda (sized types) or with the
Paco library (parameterised coinduction). Neither is used downstream;
`delay_CPO_requires_quotient` does not depend on either admitted lemma.

---

## DD-008: HB instance ordering for `PointedCPO`

**Decision:** For any type `T`, the three instance registrations
`lift_IsCPO`, `lift_HasBottom`, `lift_IsPointed` must appear in exactly
this order.

**Rationale:**

The HB mixin declaration for `IsPointed` reads:
```coq
HB.mixin Record IsPointed T of CPO T & HasBottom T := {
  bottom_least : forall (x : T), ⊥ ⊑ x;
}.
```

The `of CPO T & HasBottom T` clause means HB requires both `CPO T` and
`HasBottom T` to already be registered before `IsPointed T` can be
instantiated. Specifically:

- `lift_HasBottom` must follow `lift_IsCPO` (because `HasBottom`
  depends on `HasLe`, which is also a prerequisite of `IsCPO` — HB
  checks the full diamond structure).
- `lift_IsPointed` must follow both.

Violating this order causes a silent HB elaboration failure (no error
message; the instance simply does not register). This was the source of
a bug in an early draft of `Lift.v` where `HasBottom` and `IsPointed`
were declared immediately after the `PartialOrder` instances in §2,
before `IsCPO` was registered in §3.

**Rule:** When building a `PointedCPO`, always register in the order:
`HasLe → IsPreorder → IsPartialOrder → HasSup → IsCPO → HasBottom → IsPointed`.