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

The first iteration of the codebase had a `Pointed.v` that was a
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
- `src/theory/EnrichedTheory.v` — derives the joint form
  (`comp_joint_continuous`, `comp_joint_cont_fun`) from the separate
  axioms + `Products.v`; see DD-016 for the two-stage proof strategy

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
- `src/lang/PCF_Syntax.v` — 804 lines
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

---

## DD-014: Soundness by structural induction on Eval

**Decision:** The soundness theorem (`PCF_Soundness.v`) is proved by
structural induction on the big-step evaluation derivation `H : e ⇓ v`,
using the computation rules and substitution lemmas from
`PCF_Denotational.v` directly — no auxiliary lemmas outside the file.

**Rationale:**

In the CBV big-step setting, soundness has the form
`e ⇓ v → sem_exp e tt = Some (sem_val v tt)`. Each evaluation rule
corresponds exactly to a computation rule (`sem_exp_LET`, `sem_exp_APP`,
`sem_exp_IFB`, etc.) plus induction hypotheses. The two non-trivial
cases (LET and APP) require the substitution interface:

- LET: `sem_single_subst` reduces `sem_exp (singleSubstExp w₁ e₂) tt`
  to `sem_exp e₂ (sem_val w₁ tt, tt)`.
- APP: `sem_double_subst` + `sem_val_FIX_unfold` reduce the application
  to the body under double substitution.

These two interface lemmas (`sem_single_subst`, `sem_double_subst`) are
proved locally in `PCF_Soundness.v §1` by composing `sem_exp_subst` with
`sem_subst_single`/`sem_subst_double` from `PCF_Denotational.v §9`.

Three corollaries are derived:
- `soundness_not_none`: convergence implies non-⊥ denotation
- `soundness_val`: `VAL v` denotes `Some (sem_val v tt)`
- `soundness_denotation_agree`: co-evaluating terms have equal denotations

**Affected files:**
- `src/lang/PCF_Soundness.v` — 261 lines

---

## DD-015: Adequacy via Benton-Kennedy-Varming logical relation

**Decision:** Computational adequacy (`PCF_Adequacy.v`) is proved via a
type-indexed logical relation following Benton–Kennedy–Varming §3.2, with
the relation defined by structural recursion on `Ty`.

**Rationale:**

The adequacy theorem states `sem_exp e tt <> None → e ⇓`. The standard
proof technique is a logical relation bridging syntax and semantics. Two
design choices were made:

1. **Value + expression relations (not just one):** We define
   `rel_val τ : sem_ty τ → CValue τ → Prop` and
   `rel_exp τ : option (sem_ty τ) → CExp τ → Prop` where `rel_exp` is
   the "lift" of `rel_val`:
   ```
   rel_exp τ None     e := True
   rel_exp τ (Some d) e := ∃ v, e ⇓ v ∧ rel_val τ d v
   ```
   This cleanly handles the option-monad structure of the denotation.

2. **Arrow case uses `doubleSubstExp`:** A function denotation `f` is
   related to `v` iff `v = FIX τ₁ τ₂ body` and for all related inputs
   `(d₁, v₁)`, applying `f` to `d₁` is related to
   `doubleSubstExp v₁ v body`. This directly mirrors the operational
   rule `e_App`, avoiding an intermediate application form.

3. **FIX case via `fixp_ind`:** The denotation of `FIX` is a Kleene
   fixed point. We apply Scott's fixed-point induction principle
   (`fixp_ind`) with a pointwise predicate. Admissibility of `rel_exp`
   is proved via `rel_val_admissible` (by induction on `τ`) and the
   chain-stabilisation properties of the lift CPO (`lift_sup_some_eq`,
   `chain_some_stable`, `D_chain_fn_eq`).

4. **Classical logic:** The file imports `Classical` (for
   `excluded_middle` in the admissibility proofs) but does not use
   `ClassicalEpsilon` beyond what `Lift.v` already requires.

5. **Product case uses `dependent destruction`:** The product case in
   `rel_val_admissible` uses `dependent destruction` from
   `Program.Equality` to invert the `PAIR` equality. This introduces
   `JMeq_eq` in the proof term but only at the `Prop` level (relating
   values, not computing with them), so it does not cause the
   computation-blocking issues described in DD-013.

The fundamental lemma is proved by mutual induction on `Value`/`Exp`
using the `Combined Scheme val_exp_ind`. The adequacy theorem follows
from instantiating the fundamental lemma at the empty environment.

The full correspondence `e ⇓ ↔ sem_exp e tt <> None` combines soundness
(forward direction) with adequacy (converse).

**Affected files:**
- `src/lang/PCF_Adequacy.v` — 820 lines

---

## DD-016: HB coercion workarounds in `EnrichedTheory.v`

**Decision:** `EnrichedTheory.v` (706 lines) uses a systematic set of
HB coercion workarounds — `etransitivity`, explicit `@`-qualified
projections, `unshelve econstructor`, `Arguments {C}` directives, and
`cbn [mf_fun]` / `cbv beta` normalization — to compile from source
rather than from `.vo` files.

**Rationale:**

When building `EnrichedTheory.v` with `dune build` (compiling from
source), HB canonical structure resolution fails in several contexts
that work fine when loading from `.vo` files in the IDE. The core
problem is that HB-synthesized coercion paths (e.g.,
`CPOEnrichedCat.sort` → `CPO.sort`) resolve ambiguously or fail to
unify when the elaborator encounters intermediate terms with
under-determined types. Five categories of workarounds were identified:

1. **`etransitivity` instead of `le_trans with X`:** The `with X` clause
   forces Rocq to elaborate `X` immediately, which triggers HB
   canonical-structure search on the intermediate term. When
   `CPOEnrichedCat.sort` and `CPO.sort` offer competing coercion paths,
   this search fails. `etransitivity` defers the intermediate term to a
   unification variable, letting each half of the transitivity chain
   resolve independently.

2. **Explicit `@` for HB projections:** Writing `@comp_assoc C A B C' D`
   instead of `comp_assoc` and `@le_refl (hom A B) f` instead of
   `le_refl` provides enough type information for HB to resolve the
   correct structure instance without ambiguity.

3. **`unshelve econstructor` for record construction:** Building records
   like `lc_functor` and `ep_pair` with `refine {| ... |}` causes HB to
   attempt structure resolution on each field simultaneously, which
   fails. `unshelve econstructor` constructs the record one field at a
   time, giving the tactic engine more control over elaboration order.

4. **`Arguments lcf_obj {C}` directives:** Record projections for
   `lc_functor` default to making all arguments explicit. Adding
   `Arguments ... {C}` makes the enriched-category argument implicit,
   matching HB's conventions and preventing resolution failures at call
   sites.

5. **`cbn [mf_fun]` + `cbv beta` before rewrites:** HB-wrapped terms
   often contain nested coercions that prevent `rewrite` from matching
   the LHS. Selectively unfolding `mf_fun` (the innermost coercion) and
   then beta-reducing exposes the term structure that `rewrite` expects.

**Additional architectural choice — product-free joint continuity (§2):**

Joint continuity of composition (`comp_joint_continuous`) is proved
via a two-stage approach:

- **Stage A** (product-free): Proves `comp_joint_sup` using only
  `comp_chain` (a chain of compositions `f.[n] ⊚ g.[n]`) and the
  diagonal argument. No product CPO types appear in the proof terms,
  avoiding coercion-path conflicts between `CPO.sort` and
  `CPOEnrichedCat.sort`.

- **Stage B** (product packaging): Wraps the Stage A result into a
  `cont_fun (hom B C * hom A B) (hom A C)` by using the product CPO
  projections to extract chains and applying Stage A. The coercion
  conflicts are confined to the thin packaging layer.

This two-stage split was necessary because a direct proof over the
product CPO type caused irreconcilable HB coercion failures throughout
the transitivity and rewriting steps.

**Affected files:**
- `src/theory/EnrichedTheory.v` — 706 lines (§1–§4)

---

## DD-017: `IsMixedLocallyContinuous` axiom design in `DomainEquations.v`

**Decision:** The `IsMixedLocallyContinuous` HB mixin in
`DomainEquations.v` axiomatises the mixed-variance bifunctor `MF_mor`
via six fields — identity, composition, separate monotonicity (left/right),
and separate continuity (left/right) — rather than using joint continuity
or joint monotonicity.

**Rationale:**

The mixed-variance bifunctor `MF_mor` takes a contravariant argument
and a covariant argument:
```coq
MF_mor : forall {A1 A2 B1 B2}, hom A2 A1 -> hom B1 B2 ->
         hom (MF_obj A1 B1) (MF_obj A2 B2)
```

Joint monotonicity and joint continuity (`MF_mor_mono`, `MF_mor_joint_sup`)
are *derived* from the separate axioms in the `MFDerived` section. This
mirrors the same strategy used in DD-002 for composition continuity:
separate axioms avoid importing `Products.v` at the mixin declaration
point.

Additionally:
- Monotonicity fields (`MF_mor_mono_l`, `MF_mor_mono_r`) precede
  continuity fields (`MF_mor_cont_l`, `MF_mor_cont_r`), following DD-003.
- The `mf_mor` wrapper definition pins the carrier to
  `MixedLCFunctor.type`, working around an HB canonical-structure
  resolution issue where `MF_Obj`'s carrier sort does not unify with
  `MixedLCFunctor.sort`.

**The `bilimit_exists` axiom:**

`DomainEquations.v` contains one `Axiom`:
```coq
Axiom bilimit_exists :
  forall {C : MixedLCFunctor.type} (D0 : C)
         (ep0 : ep_pair D0 (MF_obj D0 D0)),
    BilimitData D0 ep0.
```

This axiom asserts the existence of the bilimit (inverse limit) of the
approximation sequence `D0, F(D0,D0), F(F(...),F(...)), ...`. Its proof
requires constructing the omega-product CPO `∏_n D_n` (the product of
countably many CPOs) and carving out the coherent sub-CPO
`{ (d_n) | p_n(d_{n+1}) = d_n }`. The omega-product construction is not
yet in the library (it requires an infinite-product CPO, not just binary
products). Following Benton-Kennedy §4 and A&J §3.3.7, the axiom is
acceptable for the thesis; the `BilimitData` record precisely specifies
the proof obligation.

All consequences of the bilimit (D_inf, ROLL/UNROLL, the isomorphism
`D_inf ≅ F(D_inf, D_inf)`, the deflation chain, and `bil_sup_deflations`)
are fully proved from the record fields — no additional axioms or admits.

**Affected files:**
- `src/theory/DomainEquations.v` — 446 lines (§1–§7)

---

## DD-018: `nat_trans` as a plain record over `lc_functor`

**Decision:** Natural transformations in `NatTrans.v` are defined as a
plain `Record nat_trans` (not an HB structure) parameterised over two
`lc_functor` values, not over HB `LocallyContinuousFunctor` instances.

**Rationale:**

The `lc_functor` plain record (from `EnrichedTheory.v`) was chosen over
the HB `LocallyContinuousFunctor` structure for two reasons:

1. **Universe consistency:** Registering HB instances for functors on
   `CPOEnrichedCat.type` triggers universe inconsistencies when natural
   transformations attempt to quantify over all objects `X : C` in the
   enriched category. The `lc_functor` record avoids HB's universe
   machinery entirely.

2. **Composability:** Identity, vertical composition, and horizontal
   composition (whiskering) of natural transformations produce new
   `nat_trans` values. With HB structures, each composition would need
   a new HB instance registration, which is cumbersome and error-prone.
   Plain records compose directly.

The CPO structure on natural transformations (pointwise order, chains,
suprema) is proved directly on `nat_trans` without HB instance
registration — the `nat_trans` type is not a general-purpose carrier
but a proof-theoretic tool.

**Affected files:**
- `src/theory/NatTrans.v` — 518 lines (§1–§6)

---

## DD-019: Yoneda lemma in `instances/Yoneda.v`

**Decision:** The representable functor `Hom(X,-)` and the enriched
Yoneda lemma live in `instances/Yoneda.v` rather than in `NatTrans.v`.

**Rationale:**

The representable functor requires the concrete CPO-enriched category
instance (`CPO.type` with `cont_fun` as hom-CPOs), which is registered
in `instances/Function.v`. Placing the Yoneda material in `NatTrans.v`
(a theory file) would create a dependency from `theory/` to `instances/`,
violating the build-order constraint:
```
DomainTheory.Theory → DomainTheory.Instances  (allowed)
DomainTheory.Instances → DomainTheory.Theory  (NOT allowed in reverse)
```

By placing Yoneda in `instances/`, the dependency chain is:
`NatTrans.v` (theory) → `Yoneda.v` (instances) → `Function.v` (instances).

The Yoneda lemma establishes an isomorphism (as an `ep_pair`) between
`nat_trans (repr_functor X) F` and `lcf_obj F X`, with both directions
(`yoneda_eval`, `yoneda_embed`) and both round-trip laws
(`yoneda_eval_embed`, `yoneda_embed_eval`) fully proved.

**Affected files:**
- `src/instances/Yoneda.v` — 443 lines

---

## DD-020: `FunLift.v` proof strategy — `change` tactic for coercion bypass

**Decision:** The six axiom proofs in `FunLift.v` (identity, composition,
separate monotonicity, separate continuity) use the `change` tactic to
normalize coercion-wrapped goals to their known reduced forms, rather than
`rewrite FL_mor_some` or `unfold FL_mor, lift_map; rewrite kleisli_some`.

**Rationale:**

After `cont_fun_ext; intro x; destruct x`, the `Some h` branch produces
goals where `FL_mor f g (Some h)` is wrapped in HB-generated coercion
chains (from `cont_fun` to its underlying function). These coercions
prevent `rewrite FL_mor_some` from matching the LHS.

Two alternative strategies were tried and fail:

1. **`unfold FL_mor, lift_map; rewrite kleisli_some`:** After `unfold`,
   the term `kleisli (cont_comp ret (FL_sandwich f g)) (Some h)`
   iota-reduces immediately during elaboration, so the `kleisli` head
   symbol disappears. There is no `kleisli ... (Some ...)` pattern left
   for `rewrite` to find.

2. **`subst mono_f; unfold FL_mor, lift_map`:** When `FL_mor` is bound
   via `set mono_f := ...`, the `set` variable prevents `unfold FL_mor`
   from seeing through the binding. `subst` removes it, but then the
   iota-reduction issue from (1) recurs.

The working strategy uses `change` to assert the known reduced form
directly:
```coq
change (Some (FL_sandwich (⊔ fs) g h) =
        (⊔ (map_chain mono_f fs)) (Some h)).
```

Key details:
- `change` bypasses coercions entirely: it only checks definitional
  equality between the stated term and the actual goal.
- Parenthesization matters: `(⊔ (map_chain mono_f fs)) (Some h)` wraps
  the sup before applying it to `Some h`. Without the parentheses, Rocq
  parses the application differently.
- The None case uses `lift_sup_none` (proving `⊔ c = None` when all
  chain elements are `None`) rather than `le_antisym`, which triggers
  canonical-structure path mismatches between `CPO` and `PartialOrder`
  for the `⊑` relation on lift types.

**Affected files:**
- `src/instances/FunLift.v` — 298 lines

---

## DD-021: Example file design patterns

**Decision:** The four worked example files (`examples/*.v`) use `apply`
rather than `exact` for HB-generated accessor lemmas, and `sem_cexp` /
`sem_cval` wrappers rather than raw `sem_exp e tt` / `sem_val v tt`.

**Rationale:**

1. **`apply` vs `exact`:** HB accessor lemmas such as `comp_id_l`,
   `comp_id_r`, `comp_assoc` have implicit arguments resolved through
   HB canonical structure unification. Within `Section` contexts that
   bind variables of type `CPOEnrichedCat.type`, `exact (comp_id_l f)`
   fails to resolve the enriched-category implicit argument, while
   `apply comp_id_l` succeeds because tactic unification has more
   flexibility. The examples use `apply` uniformly.

2. **`sem_cexp` wrappers:** In `pcf_examples.v`, stating goals as
   `sem_exp (APP pcf_id (NLIT 5)) tt = ...` fails because the Coq
   elaborator cannot coerce `tt : unit` to
   `Preorder.sort (CPO.CPO.Exports.CPO_CPO__to__Order_Preorder (sem_env []))`.
   The issue is that `sem_env [] = unit` as a `CPO.type`, but `tt`
   has bare Coq type `unit`, and the coercion chain from `unit` to the
   HB-packed carrier `Preorder.sort ...` is not inserted automatically.
   Using the wrapper `sem_cexp e` (which internally applies the semantic
   function to `tt` at the correct type) avoids the coercion problem.

3. **`FIX`-based denotation opacity:** Denotational semantics of programs
   involving `FIX` go through the `fixp` operator, which does not reduce
   by computation (its definition involves an opaque supremum). Therefore
   `reflexivity` cannot close goals like `⟦ APP pcf_id (NLIT 5) ⟧ᶜₑ = Some 5`.
   Instead, denotational results for `FIX`-based programs are obtained
   via the `soundness` theorem applied to evaluation derivations.

4. **Abstract enriched context:** `enriched_usage.v` uses
   `Context {C : CPOEnrichedCat.type}` with `Variables A B D : C`
   rather than concrete CPO.type values, so that examples work for
   any CPO-enriched category.

**Affected files:**
- `examples/basic_cpos.v` — 347 lines
- `examples/enriched_usage.v` — 234 lines
- `examples/pcf_examples.v` — 226 lines
- `examples/recursive_domain.v` — 179 lines
- `src/instances/FunLift.v` — 298 lines (§3 proofs)

---

## DD-022: Atoms-only representation with axiomatic involutive quantale for quantum CPOs

**Decision:** Quantum sets are represented as plain Rocq `Type`s (atom
indices) with Q-valued relations `qp_ord : X → X → Q`, where Q is
axiomatized as an involutive quantale via HB (`InvQuantale`). Quantum
posets are plain `Record qposet` parametrized by `Q`, not HB structures.

**Rationale:**

KLM's quantum CPO theory separates into two layers:

1. **Order theory** (§3–4, §6, §7.1–7.5): convergence, completeness,
   Scott continuity, the lift monad, enrichment, the classical embedding.
   These only need: a quantale Q, types X with Q-valued relations, and
   axioms on Q. No Hilbert spaces appear.

2. **Concrete constructions** (§2, §5, §7.6–7.7): tensor products,
   monoidal closure, algebraic compactness. These need the full
   operator-space architecture (finite-dimensional Hilbert spaces,
   completely bounded maps, Choi–Jamiołkowski). This infrastructure
   does not exist in any Rocq library.

The atoms-only approach (Option B+ from `planning/quantum.md`) was
chosen because:

- **Matches thesis scope.** Layer 1 is achievable; Layer 2 would
  require building an operator-space library from scratch.
- **Matches Rocq's strengths.** Abstract algebra via HB, not numerical
  linear algebra.
- **Already validated.** `qCPO.v` (388 lines) and `QuantumStructure.v`
  (339 lines) compile clean with this model.
- **Consistency justified.** B(H) — bounded operators on any Hilbert
  space — is a concrete involutive quantale. Its existence justifies
  the axiom set without requiring its formalization.
- **Follows KLM directly.** The Section variables in `qCPO.v` are the
  exact specification that `QuantumStructure.v` provides via HB.

**Specifics of the HB design:**

The quantale Q uses a single `HasQuantaleOps` mixin (six operations:
`q_top`, `q_bot`, `q_prod`, `q_adj`, `q_meet`, `q_inf`) and a single
`IsInvQuantale` mixin (14 axioms in five groups: top/bottom, product,
adjoint, meet, infimum). Q builds on `PartialOrder` from `Order.v`.

Quantum posets are plain `Record qposet` (not HB structures) because:
- They are parametrized by Q (an HB structure), and HB does not handle
  structures parametrized by other structures well (R5 in
  `planning/quantum.md`).
- The pattern follows `chain`, `mono_fun`, `cont_fun` — data records
  over existing HB structures.

The `qposet` record includes:
- `qp_carrier :> Type` — the atom type
- `qp_ord : X → X → Q` — Q-valued relation
- `qp_dec_eq` — decidable equality (for the Kronecker delta in antisymmetry)
- `qp_refl`, `qp_trans`, `qp_antisym` — quantum partial order axioms

**Affected files:**
- `src/quantum/QuantumStructure.v` — ~339 lines (§1–§7)
- `src/quantum/qCPO.v` — ~388 lines (§1–§10)
- `src/quantum/qCPOProperties.v` — ~1022 lines (§0–§11)
- `planning/quantum.md` — full design rationale

---

### DD-023 — Split-field `q_cont_fun` record

**Date:** 2026-03-19
**Scope:** `src/quantum/qCPOProperties.v` §1

**Decision:** The bundled quantum-continuous map record `q_cont_fun`
splits monotonicity and convergence-preservation into two separate
record fields:

```
Record q_cont_fun (X Y : qposet Q) := {
    qcf_fun   :> X -> Y;
    qcf_mono  : q_monotone qcf_fun;
    qcf_preserves : forall W K K_inf, converges K K_inf ->
        converges (map_qchain qcf_fun qcf_mono K) (fun w => qcf_fun (K_inf w));
}.
```

rather than embedding monotonicity inside an existential as in
`q_scott_continuous` from `qCPO.v`:

```
Definition q_scott_continuous f :=
    exists Hm : q_monotone f,
        forall W K K_inf, converges K K_inf ->
            converges (map_qchain f Hm K) (fun w => f (K_inf w)).
```

**Rationale:**
- `map_qchain` takes the monotonicity proof as an explicit argument.
  When composing `map_qchain G HG (map_qchain F HF K)`, the inner
  `HF` must be *the same proof witness* used to build the outer
  mapped chain. With the existential form, composing two
  `q_scott_continuous` proofs would require either destructing and
  re-packaging existentials at every use or relying on proof
  irrelevance inside non-Prop types. The split-field design avoids
  this entirely.
- A bridge lemma `q_cont_fun_scott_continuous` establishes equivalence
  with the `q_scott_continuous` predicate from `qCPO.v`.
- Follows the classical pattern: `cont_fun` in `Morphisms.v` has
  separate `cf_mono` and `cf_cont` fields, not an existential.

**Affected files:**
- `src/quantum/qCPOProperties.v` — `q_cont_fun`, all §1–§11