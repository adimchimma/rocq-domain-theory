# Design Decisions

This document records non-obvious architectural choices made during the
modernization of the Benton-Kennedy domain theory library for Rocq 9.0,
so that future contributors (and the thesis write-up) have context.

---

## DD-001: `Pointed.v` not created as a separate file

**Decision:** The content originally planned for `src/structures/Pointed.v`
(i.e. `HasBot`, `IsPointed`, `PointedCPO`) was folded directly into
`src/structures/CPO.v`, and `strict_fun` into `src/structures/Morphisms.v`.
No `Pointed.v` file is created.

**Rationale:**

The original pre-migration codebase had a `Pointed.v` that was a one-line
re-export shim:

```coq
(* old Pointed.v *)
From phase0_foundations Require Import CPO Order.
Module Pointed.
  Definition Pointed := Cpo.Pointed.
  Notation "⊥" := (@Cpo.bottom _ _).
End Pointed.
```

A re-export shim of this kind is an anti-pattern in MathComp/HB-style
libraries for two reasons:

1. **Indirection without benefit.** A user searching for `IsPointed` who
   follows `Require Import Pointed` lands in a file that immediately bounces
   them to `CPO.v`. The shim adds a conceptual layer without adding any
   definitions, lemmas, or structure.

2. **Silent change propagation.** If `HasBot` is moved or renamed in
   `CPO.v`, the shim silently changes what it re-exports; there is no
   explicit edit to `Pointed.v` to flag the change.

The better practice (following MathComp convention) is to organize files
around dependency structure, not an idealized mental model of separate
concepts. `IsPointed` has a hard dependency on `CPO T` — it belongs
in `CPO.v`. `strict_fun` has a hard dependency on `cont_fun` — it belongs
in `Morphisms.v`. A downstream file that wants both writes:

```coq
From DomainTheory.Structures Require Import CPO Morphisms.
```

which is fully explicit and requires no intermediary.

**Affected files:**
- `src/structures/CPO.v` — contains `HasBot`, `IsPointed`, `PointedCPO`
- `src/structures/Morphisms.v` — contains `strict`, `strict_fun`,
  `strict_id`, `strict_comp`
- `src/structures/Pointed.v` — **not created**
- `src/structures/dune` — must not list `Pointed` as a module

---

## DD-002: Separate continuity axioms in `IsCPOEnriched`

**Decision:** `IsCPOEnriched` axiomatises composition via two separate
Scott-continuity conditions (`comp_cont_l` and `comp_cont_r`) rather than
a single joint continuity condition on the product.

**Rationale:**

The "natural" statement of CPO-enrichment is that composition

```
comp : Hom(A,B) × Hom(B,C) → Hom(A,C)
```

is jointly Scott-continuous. However, Abramsky & Jung Lemma 3.2.6 states:

> A function f : D × E → F is Scott-continuous if and only if it is
> Scott-continuous in each variable separately.

So the two formulations are equivalent. We choose separate continuity
because the joint form would require importing `Products.v` (for the
product CPO `Hom(A,B) × Hom(B,C)`) at the point where `Enriched.v` is
declared, creating a forward dependency cycle:

```
Enriched.v → Products.v → CPOTheory.v → Enriched.v  (cycle)
```

Using separate continuity breaks the cycle entirely: `Enriched.v` depends
only on `Order.v`, `CPO.v`, and `Morphisms.v`.

This is precisely the strategy used in Kornell-Lindenhovius-Mislove (2024)
§3.3 to prove qCPO is enriched over CPO (Theorem 3.3.5): they prove
separate continuity in each variable (Lemmas 3.3.3–3.3.4) rather than
joint continuity directly.

**Affected files:**
- `src/structures/Enriched.v` — `IsCPOEnriched.comp_cont_l/r`
- `src/theory/EnrichedTheory.v` — should prove the joint form as a derived
  lemma once `Products.v` is available

---

## DD-003: Monotonicity fields precede continuity fields in HB mixins

**Decision:** In every mixin where both monotonicity and Scott-continuity
are required (`IsCPOEnriched`, `IsLocallyContinuous`), the monotonicity
field is declared *before* the continuity field.

**Rationale:**

The `continuous` predicate in `Morphisms.v` takes a `mono_fun` as its
argument. `Build_mono_fun` requires a proof of monotonicity. If a
continuity field appears before the monotonicity field in an HB mixin,
the proof term `Build_mono_fun (fun x => ...) comp_mono_l` in the
continuity field has no `comp_mono_l` in scope yet (because HB processes
mixin fields top-to-bottom). Placing monotonicity first ensures the
proof compiles.

This is a Rocq-HB implementation detail, not a mathematical preference.

---

## DD-004: Leibniz equality for categorical laws

**Decision:** The categorical laws in `IsCPOEnriched` (`comp_id_l`,
`comp_id_r`, `comp_assoc`) and in `IsLocallyContinuous` (`F_mor_id`,
`F_mor_comp`) use Leibniz equality `=` rather than setoid equality `==`.

**Rationale:**

The hom-CPOs in our framework are HB-packed types (`CPO.type`), and the
equality on their elements is Leibniz equality by default (we do not
currently attach a setoid structure to every CPO). Using `=` keeps the
categorical laws definitionally true and avoids the overhead of setoid
rewriting infrastructure at the structure level.

If a concrete instance (e.g. the function-space CPO) uses a coarser
extensional equality `f == g ↔ ∀ x, f x = g x`, the laws should be
restated using `==` in the relevant theory file (`EnrichedTheory.v` or
the instance file). See also Benton-Kennedy §2.1, which uses `==`
throughout but notes the tension between pointwise and point-free styles.

---

## DD-005: `HasMixedEndo` records only data; axioms deferred

**Decision:** The mixin `HasMixedEndo` in `Enriched.v` contains only the
object and morphism action of a mixed-variance bifunctor. The functoriality
and local-continuity axioms are deferred to `src/theory/DomainEquations.v`.

**Rationale:**

The full axioms for a mixed-variance locally continuous bifunctor
(A&J Definition 5.2.5, Benton-Kennedy `BiFunctor` record) require
reasoning about directed sets of pairs of morphisms, which in turn
requires the product CPO construction. Declaring the axioms in `Enriched.v`
would create the same forward-dependency cycle described in DD-002.

By splitting data (`HasMixedEndo` in `Enriched.v`) from axioms
(`IsMixedLocallyContinuous` in `DomainEquations.v`), the structures file
stays dependency-minimal and the full theory becomes available exactly when
the bilimit construction needs it.