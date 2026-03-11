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

---

## DD-009: Intrinsic typing and ANF for PCFv

**Decision:** PCF syntax (`lang/PCF_Syntax.v`) uses intrinsically typed
terms in Administrative Normal Form (ANF), with separate mutually
inductive `Value` and `Exp` types indexed by `Env` and `Ty`. Variables
are typed de Bruijn indices (`Var Γ τ`). Renamings are defined before
substitutions, bootstrapping the latter (McBride's technique).

**Rationale:**

Benton–Kennedy §3 describe two approaches tried during the original
formalization:

1. **Extrinsic typing** (first attempt): raw `Value`/`Exp` with `nat` de
   Bruijn indices, plus a separate typing judgment `VTy Γ τ v : Type`.
   This required lengthy proofs that any two typing derivations of the
   same term are equal, and all definitions and theorems needed
   well-formedness side-conditions.

2. **Intrinsic typing** (final design): `Value : Env → Ty → Type` and
   `Exp : Env → Ty → Type`, where well-typedness is ensured by
   construction. "Definitions and theorems become more natural and much
   more concise, and the problems with equality proofs go away."
   (Benton–Kennedy §3)

We adopt the intrinsic approach directly, with the following specifics:

- **ANF**: arguments to function calls must be values; intermediate
  computation is sequenced by `LET`. This matches Benton–Kennedy exactly.
- **`FIX` binds two variables**: `FIX τ₁ τ₂ body` where index 0 is the
  argument (`x : τ₁`) and index 1 is the self-reference (`f : τ₁ →ₜ τ₂`).
- **`OP` is parametric**: takes any Rocq function `nat → nat → nat`,
  keeping the syntax minimal.
- **No `TyLift`**: classical PCFv doesn't need it; the denotational
  semantics handles lifting by interpreting base types as pointed CPOs.
- **Typed de Bruijn via `Var`**: `ZVAR` and `SVAR` witnesses rather than
  raw `nat` indices. This eliminates the need for `nth_error Γ n = Some τ`
  proofs.
- **Renaming bootstrap**: general renamings (`Ren Γ Γ'`) are defined
  first, then substitutions (`Subst Γ Γ'`) use renamings for the shift
  operation. This avoids a complex dependent shift operator
  `Val(Γ ++ Γ') τ → Val(Γ ++ [τ'] ++ Γ') τ` (McBride; Altenkirch & Reus
  1999; Benton–Kennedy §3).

**Naming changes from Benton–Kennedy:**

| Benton–Kennedy (2009) | rocq-domain-theory | Notes |
|------------------------|--------------------|-------|
| `TINT n` | `NLIT n` | "N for Nat" |
| `TBOOL b` | `BLIT b` | "B for Bool" |
| `TVAR i` | `VAR v` | |
| `TFIX e` | `FIX τ₁ τ₂ body` | Explicit type indices |
| `TPAIR v1 v2` | `PAIR v1 v2` | |
| `TVAL v` | `VAL v` | |
| `TLET e1 e2` | `LET e1 e2` | |
| `TAPP f v` | `APP f v` | |
| `TFST v` / `TSND v` | `FST v` / `SND v` | |
| `TOP op v1 v2` | `OP op v1 v2` | |
| `TGT v1 v2` | `GT v1 v2` | |
| `TIF b e1 e2` | `IFB b e1 e2` | |
| `Int` / `Bool` | `Nat` / `Bool` | `Int` → `Nat` (values are `nat`) |

The `T` prefix (for "typed") was dropped since all terms are typed by
construction.

**Affected files:**
- `src/lang/PCF_Syntax.v` — 512 lines
- `src/lang/PCF_Operational.v` — uses `CValue`/`CExp` from PCF_Syntax
- `src/lang/PCF_Denotational.v` — uses the same syntax

---

## DD-010: Big-step CBV evaluation for PCFv

**Decision:** The operational semantics (`lang/PCF_Operational.v`) uses
a big-step evaluation relation `Eval : CExp τ → CValue τ → Prop`
(notation `e ⇓ v`), not a small-step reduction relation.

**Rationale:**

Benton–Kennedy §3 use big-step evaluation for typed PCFv:
> "the operational semantics can be presented very directly"

The big-step relation matches better with the denotational semantics for
CBV, where the soundness theorem has the form `e ⇓ v → ⟦e⟧ = η(⟦v⟧)`.
With small-step semantics, one would need to relate each reduction step
to denotational equality, requiring a subject-reduction/preservation
theorem.

With intrinsically typed closed terms, there are no stuck states:
- Every `CValue τ` is a value by construction (no `value` predicate needed)
- Every `CExp τ` either diverges (no `Eval` derivation) or evaluates
- No progress/preservation theorems are needed

The `e_App` rule requires the function value to be `FIX τ₁ τ₂ body` —
this is the only possibility for a closed value of function type, since
there are no free variables.

**Affected files:**
- `src/lang/PCF_Operational.v` — 332 lines
- `src/lang/PCF_Soundness.v` — will use induction on `Eval`
- `src/lang/PCF_Adequacy.v` — adequacy statement uses `Converges`

---

## DD-011: Point-free mutual fixpoint for `sem_val`/`sem_exp`

**Decision:** The denotation functions `sem_val : Value Γ τ → [sem_env Γ →c sem_ty τ]`
and `sem_exp : Exp Γ τ → [sem_env Γ →c option (sem_ty τ)]` are defined as a
single mutual structural `Fixpoint`, with each case expressed as a point-free
composition of library combinators (no explicit destructuring of environments).

**Rationale:**

Two approaches were evaluated:

1. **Three-pass approach:** Define raw functions `sem_val_fn`/`sem_exp_fn`
   first, prove monotonicity in a second pass, prove continuity in a third,
   then package as `cont_fun`. This gives separate lemmas at each stage but
   multiplicates proof obligations — every case must be handled three times.

2. **Point-free single-pass:** Each syntactic case is a pipeline of library
   combinators (`cont_comp`, `cont_pair`, `cont_curry`, `cont_flip`, `FIXP`,
   `kleislir`, `ret`, etc.) that are already packaged as `cont_fun`. The
   mutual fixpoint directly produces `cont_fun` values with no extra proof
   obligations.

The single-pass approach was chosen because:
- The combinator library (`FunctionSpaces.v`, `Products.v`, `Lift.v`,
  `Function.v`) already provides all needed packaging.
- The FIX case benefits from `FIXP : [[D →c D] →c D]` being a single
  continuous operator — no manual monotonicity/continuity threading.
- The computation rules (§7) reduce by `reflexivity` for all cases except
  FIX, which uses `FIXP_is_fixedpoint`.

The downside is that `simpl` over `sem_val`/`sem_exp` unfolds all combinator
internals, producing unreadable goals. This is mitigated by:
- Using `change` rather than `simpl` in proofs (§8, §9).
- Making `sem_ren` `Opaque` during the renaming/substitution mutual proofs.

**Affected files:**
- `src/lang/PCF_Denotational.v` — §4 (mutual fixpoint definition)

---

## DD-012: Renaming route for the substitution lemma

**Decision:** The substitution lemma (`sem_val_subst`/`sem_exp_subst`) is
proved via an intermediate **renaming route**: first proving the renaming
lemma (`sem_val_ren`/`sem_exp_ren`) by mutual induction, then using the
renaming lemma to prove `sem_subst_ext` (which requires `sem_val_wk`,
which requires `sem_val_ren`), and finally proving the substitution lemma
by mutual induction using `sem_subst_ext`.

**Rationale:**

The direct approach to `sem_subst_ext` requires knowing that
`sem_val (wkVal v) (x, γ) = sem_val v γ`, i.e. that syntactic weakening
(`wkVal`) corresponds to dropping the first environment component. Since
`wkVal v = renVal ren_wk v`, this requires the renaming lemma.

The dependency chain is:
```
sem_ren_ext  (renaming preserves env extension)
    ↓
sem_val_ren / sem_exp_ren  (mutual induction on terms)
    ↓
sem_ren_wk   (weakening drops outermost component)
    ↓
sem_val_wk   (syntactic weakening = semantic projection)
    ↓
sem_subst_ext  (substitution preserves env extension)
    ↓
sem_val_subst / sem_exp_subst  (mutual induction on terms)
```

This is exactly the bootstrapping strategy described in Benton–Kennedy §3:
"first composition of renamings is defined, then composition of substitution
with renaming, and finally composition of substitutions." Our semantic
lemmas mirror this syntactic bootstrapping.

**Key proof technique:** During the mutual induction proofs for
`sem_val_ren`/`sem_exp_ren` and `sem_val_subst`/`sem_exp_subst`, `sem_ren`
is made `Opaque` to prevent `simpl`/`change` from unfolding it. It is made
`Transparent` again immediately after. The FIX case in each mutual proof
uses `cont_fun_ext` to reduce the goal to three nested extensionality
steps, then applies the IH on the body with two `ren_ext`/`subst_ext`
applications.

**Affected files:**
- `src/lang/PCF_Denotational.v` — §8 (renaming), §9 (substitution)

---

## DD-013: `var_case` combinator for `ren_ext` and `subst_ext`

**Decision:** The renaming extension `ren_ext` and substitution extension
`subst_ext` in `PCF_Syntax.v` are defined using a `var_case` combinator
that eliminates the head variable by pattern matching with a
function-returning return type, rather than matching with an `eq_rect` or
`JMeq_eq` cast.

**Rationale:**

The typed de Bruijn variable `Var (τ :: Γ) σ` can be either `ZVAR`
(where `σ = τ` by the index) or `SVAR x` (where `x : Var Γ σ`). To
define `ren_ext` and `subst_ext`, we need to case-split on whether a
variable refers to the newly bound position or a previous one. The naïve
`match` produces goals with `JMeq_eq` or `eq_rect` casts because the
type indices change across branches. The `var_case` combinator avoids
this by using a dependent match with a return type of the form
`(fun T => ...) σ`:

```coq
Definition var_case {Γ τ A}
    (z : A τ) (s : forall σ, Var Γ σ → A σ) {σ} (x : Var (τ :: Γ) σ) : A σ :=
  match x in Var G σ return
    match G with [] => unit | τ' :: Γ' => A τ' → (forall ρ, Var Γ' ρ → A ρ) → A σ end
  with
  | ZVAR      => fun z _ => z
  | SVAR x'   => fun _ s => s _ x'
  end z s.
```

This computes cleanly: `var_case z s ZVAR = z` and
`var_case z s (SVAR x') = s _ x'` hold by `reflexivity`, with no opaque
equality transports. The benefit appears in `sem_ren_ext` and
`sem_subst_ext` where the proofs reduce via kernel conversion.

**Affected files:**
- `src/lang/PCF_Syntax.v` — `var_case`, `ren_ext`, `subst_ext` definitions