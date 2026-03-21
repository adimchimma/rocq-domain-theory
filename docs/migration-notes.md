# Migration Notes: Benton-Kennedy-Varming (2009) → rocq-domain-theory

This document compares, section by section, the domain theory
formalization described in Benton, Kennedy & Varming's paper *"Some
Domain Theory and Denotational Semantics in Coq"* (2009) with the
current `rocq-domain-theory` library.

**Important caveat.** We compare against BKV's *paper description*,
not their Coq artifact (which we do not have access to). Where BKV
describe a construction or proof strategy in prose, we note what they
describe; where they show Coq code in the paper, we cite it. We do
not speculate about implementation details the paper omits.

**References:**

- **BKV**: Benton, Kennedy & Varming, "Some Domain Theory and
  Denotational Semantics in Coq" (2009)
- **A&J**: Abramsky & Jung, "Domain Theory" (1994)
- **KLM**: Kornell, Lindenhovius & Mislove, "Quantum CPOs" (2024)

---

## Summary of Major Differences

| Aspect | BKV paper | rocq-domain-theory |
|--------|-----------|-------------------|
| Proof assistant | Coq (version unspecified) | Rocq 9.0 |
| Structuring | Coq `Module`/`Record` | HB packed-class hierarchy |
| CPO base | Preorder (BKV §2) | `PartialOrder` (follows A&J Def. 2.1.13) |
| Equality | Setoid `==` throughout (BKV §2) | Leibniz `=` (see DD-004) |
| Lift monad | Coinductive `delay D` (BKV §2.2) | Flat `option D` with `ClassicalEpsilon` (see DD-006) |
| Function-space sup | Described abstractly | Proved constructively (882 lines) |
| Sum sup | Described abstractly | Proved constructively (624 lines) |
| Lift sup | Described abstractly | Proved via `ClassicalEpsilon` (647 lines) |
| Domain equations | Approximation sequences, bilimit (BKV §4) | Full framework; 1 axiom (`bilimit_exists`) |
| Enriched categories | Implicit (self-enrichment of CPO) | Explicit HB structure (`CPOEnrichedCat`) |
| PCF syntax | Intrinsic, ANF, `T`-prefixed constructors | Same design; renamed constructors |
| PCF adequacy | Proof strategy described (§3.2) | Fully proved (820 lines) |
| Quantum extensions | Not present | qCPOs following KLM (2024) |

---

## Domain Theory Layer

---

### Orders and CPOs (BKV §2)

**BKV describe:** A `preorder` record with fields `carrier`, `le`,
`le_refl`, `le_trans`. CPOs are preorders equipped with least upper
bounds of chains (`lub_of_chain`, `lub_upper`, `lub_least`). Pointed
CPOs add a least element. BKV do not require antisymmetry at the
preorder/CPO level — they note this is standard.

**rocq-domain-theory:** HB hierarchy with explicit mixins:
```
HasLe → IsPreorder → Preorder
              └── IsPartialOrder → PartialOrder

HasSup + PartialOrder → IsCPO → CPO
HasBot + CPO → IsPointed → PointedCPO
```

| BKV description | Our implementation | Notes |
|-----------------|-------------------|-------|
| `Record preorder` with explicit `carrier` | `Preorder.type` with HB sort coercion | No `.carrier` projections needed |
| CPO on preorder | CPO requires `PartialOrder` | A&J Def. 2.1.13; `sup_ext` needs `le_antisym` |
| `Class Pointed` (typeclass) | `HasBottom` + `IsPointed` HB mixins | Avoids instance search surprises |
| `lub_of_chain` | `sup` (notation `⊔ c`) | |
| `lub_upper` / `lub_least` | `sup_upper` / `sup_least` | |
| Setoid equality `==` for CPO elements | Leibniz `=` | See DD-004 |

**Key semantic difference:** BKV build CPOs on preorders. We require
`PartialOrder` (antisymmetry). This follows A&J Definition 2.1.13 more
faithfully and is needed for `sup_ext` (equal chains have equal sups).
BKV's approach would require carrying `le_antisym` as a side condition
wherever `sup_ext` is used.

**What we add beyond BKV:**
- `OrderTheory.v`: setoid reasoning via `pequiv` (`x ≈ y`)
- `CPOTheory.v`: derived lemmas (`sup_mono`, `sup_ext`, `map_chain_id`)

---

### Continuous Functions (BKV §2)

**BKV describe:** Monotone functions (`mono_fun`) and continuous
functions (`cont_fun`, called `fconti` in the paper) as bundled records.
Composition is associative; identity is continuous. BKV use a separate
`Continuous` module.

**rocq-domain-theory:** Same approach — `mono_fun` and `cont_fun` as
bundled records in `Morphisms.v`. `continuous` is a predicate in `CPO.v`.

| BKV description | Our implementation | Notes |
|-----------------|-------------------|-------|
| `fconti` record (§2.1) | `cont_fun` record | Different name |
| `cf_mfun` field (mono_fun inside cont_fun) | `cf_mono` | Renamed |
| Separate `Continuous` module | `continuous` predicate in `CPO.v`, `cont_fun` in `Morphisms.v` | Consolidated |
| `cont_comp_assoc` via `proof_irrelevance` | Same strategy | `proof_irrelevance` still used |
| `g ∘ f` notation | Preserved | |

We also define `strict_fun` (strict = continuous + bottom-preserving),
which BKV do not discuss as a separate concept.

---

### Lift Monad (BKV §2.2)

**BKV describe:** A coinductive `delay D` type with constructors
`Eps` (delay step) and `Val` (result). The order is defined
coinductively, and the monad operations (`eta`/`ret`, `bind`/`kleisli`)
are corecursive. BKV describe bisimulation as the appropriate notion of
equality and use setoid equality throughout. They note the Kleisli
extension is the key construction for the monad structure.

**rocq-domain-theory:** We use the flat lift `option D` (`None` = ⊥,
`Some d` = value) instead of coinduction. See DD-006 for the full
rationale.

| BKV description | Our implementation | Notes |
|-----------------|-------------------|-------|
| Coinductive `delay D` | `option D` | Flat lift; see DD-006 |
| `Eps`/`Val` constructors | `None`/`Some` | |
| Coinductive order + bisimulation | Flat order: `None ⊑ x` always, `Some a ⊑ Some b ↔ a ⊑ b` | |
| Setoid equality (bisimulation) | Leibniz `=` | |
| Sup described abstractly | Proved via `ClassicalEpsilon` | 647 lines in `theory/Lift.v` |
| `eta`/`bind` corecursive | `ret`/`kleisli` on `option` | Direct pattern matching |
| Monad laws up to bisimulation | Monad laws up to Leibniz `=` | Simpler proofs |

**Why not coinduction?** The coinductive `delay D` type has a
fundamental antisymmetry obstruction: `now d ≠ later (now d)` (by
`discriminate`) but they are semantically equivalent (both converge to
`d`). Making `delay D` into a `CPO.type` (which uses Leibniz equality)
would require quotienting by bisimulation — requiring either setoid
CPOs, quotient types, or HITs. The flat lift avoids this entirely.

**Supplementary file:** `theory/LiftMonad.v` (488 lines) develops the
coinductive approach fully and proves precisely why it cannot form a
`CPO.type` without quotient types. This serves as a side-by-side
comparison with BKV's approach for the thesis.

---

### Function Spaces (BKV §2.1)

**BKV describe:** The function-space CPO `[D →c E]` with pointwise
order. BKV describe the pointwise sup construction `λ x. ⊔_n (c_n x)`
and note it is continuous, but the paper does not give a detailed proof
of the continuity of the pointwise sup.

**rocq-domain-theory:** `theory/FunctionSpaces.v` (882 lines) proves
the full construction:

1. The pointwise sup of continuous functions is well-defined.
2. The pointwise sup is itself continuous (the key lemma, using
   Scott-continuity of each function in the chain and commutativity of
   the double sup).
3. `curry`, `uncurry`, `eval` are proved continuous.
4. `FIXP : [[D →c D] →c D]` — the Kleene fixed-point operator packaged
   as a Scott-continuous map. BKV describe `FIXP` (§2.1) but the
   continuity proof (in `f`) is our contribution.

---

### Fixed Points (BKV §2.1)

**BKV describe:** The Kleene chain `⊥, f(⊥), f²(⊥), ...`, the
least fixed point `fixp f = ⊔ kleene_chain f`, the fixed-point property
`f(fixp f) = fixp f`, minimality, and Scott induction (`fixp_ind`) for
admissible predicates. BKV also describe `FIXP` as a continuous operator.

**rocq-domain-theory:** `theory/FixedPoints.v` (525 lines) proves all
of the above:

| BKV description | Our implementation |
|-----------------|--------------------|
| `iter f n` (n-th iterate) | `iter f n` |
| Kleene chain | `kleene_chain f` |
| `fixp f = ⊔ kleene_chain f` | Same |
| `f (fixp f) = fixp f` | `fixp_is_fixedpoint` |
| Least pre-fixed point | `fixp_least` |
| `fixp_ind` (admissible predicates) | `fixp_ind` |
| `FIXP` continuous in `f` | `FIXP` in `FunctionSpaces.v` (see above) |

---

### Products and Sums (BKV §2)

**BKV describe:** Binary products with pointwise order and componentwise
sups. Separated sums. The paper notes these constructions exist but does
not discuss the sum-sup construction in detail.

**rocq-domain-theory:**

- `theory/Products.v` (537 lines): Full proof-mode construction building
  up from `prod_le_refl` through HB instance registration. Continuous
  projections `π₁`/`π₂`, continuous pairing, `cont_prod_map`,
  `cont_swap`, and the universal property.

- `theory/Sums.v` (624 lines): The key insight is that a chain in
  `A + B` is *eventually stable* in one component (either all `inl` or
  all `inr` from some index onward), since the orderings do not mix
  constructors. The sup is the sup of the stable projection. This proof
  is constructive — no classical axioms needed.

  Note: `A + B` is *not* made a `PointedCPO` even when both `A` and `B`
  are pointed, because `inl ⊥` and `inr ⊥` are incomparable.

---

### Domain Equations (BKV §4)

**BKV describe:** Solving recursive domain equations `D ≅ F(D, D)` via
inverse limits of approximation sequences. They describe EP-pairs
(embedding-projection pairs), mixed-variance locally continuous
bifunctors, the approximation sequence `D₀, F(D₀,D₀), ...`, and the
bilimit construction. BKV note the concrete bifunctor `(A, B) ↦ [A →c B]⊥`
and the resulting recursive domain `D∞ ≅ [D∞ →c D∞]⊥`. The paper
follows A&J §5.2–5.3.

**rocq-domain-theory:**

- `theory/DomainEquations.v` (446 lines): Abstract framework.
  `IsMixedLocallyContinuous` HB mixin with 6 axiom fields.
  Approximation sequence, EP-pair lifting, `BilimitData` record.
  1 `Axiom` (`bilimit_exists`) — requires an omega-product CPO not yet
  constructed. All consequences (D∞, ROLL/UNROLL isomorphism, deflation
  chain) are fully proved from the record.

- `instances/FunLift.v` (298 lines): Concrete bifunctor
  `(A, B) ↦ [A →c B]⊥` registered as a `MixedLCFunctor` instance.

- `theory/EnrichedTheory.v` (706 lines): EP-pair infrastructure
  (`ep_pair`, `ep_id`, `ep_comp`, `ep_chain`) used by domain equations.

---

## PCF Language (BKV §3)

---

### Syntax (BKV §3)

**BKV describe:** An intrinsically typed call-by-value language (PCFv)
in Administrative Normal Form, with separate mutually inductive `Value`
and `Exp` types indexed by typing environment and type. Variables are
typed de Bruijn indices. Renamings are defined before substitutions
(McBride's technique). BKV discuss two approaches — an earlier extrinsic
attempt that was abandoned, and the final intrinsic design. BKV's paper
shows constructors prefixed with `T` (for "typed"): `TINT`, `TBOOL`,
`TVAR`, `TFIX`, `TPAIR`, `TVAL`, `TLET`, `TAPP`, `TFST`, `TSND`,
`TOP`, `TGT`, `TIF`.

**rocq-domain-theory:** `lang/PCF_Syntax.v` (804 lines) follows BKV's
final intrinsic design exactly. Changes are purely cosmetic naming:

| BKV paper (§3) | Our implementation | Notes |
|----------------|-------------------|-------|
| `Ty := Int \| Bool \| Arrow \| Prod` | `Ty := Nat \| Bool \| Arrow \| Prod` | `Int` → `Nat` (values are `nat`, not `Z`) |
| `Arrow` notation `->` | `Arrow` notation `→ₜ` | Subscript avoids clash with Rocq `→` |
| `Prod` notation `*` | `Prod` notation `×ₜ` | Subscript avoids clash with Rocq `*` |
| `TINT n` | `NLIT n` | Dropped `T` prefix |
| `TBOOL b` | `BLIT b` | |
| `TVAR i` | `VAR v` | |
| `TFIX e` | `FIX τ₁ τ₂ body` | Explicit type indices in constructor |
| `TPAIR v1 v2` | `PAIR v1 v2` | |
| `TVAL v` | `VAL v` | |
| `TLET e1 e2` | `LET e1 e2` | |
| `TAPP f v` | `APP f v` | |
| `TFST`/`TSND v` | `FST`/`SND v` | |
| `TOP op v1 v2` | `OP op v1 v2` | |
| `TGT v1 v2` | `GT v1 v2` | |
| `TIF b e1 e2` | `IFB b e1 e2` | |
| `Subst Γ Γ'` | Same | Unchanged |
| `substVal`/`substExp` | `substVal`/`substExp` | Same names |
| `singleSubst`/`doubleSubst` | `single_subst`/`double_subst` | Snake_case |

**What we add beyond BKV:** The `var_case` combinator (see DD-013)
for definitionally-computing case analysis on de Bruijn variables,
avoiding `JMeq_eq` opacity. This ensures `single_subst v τ ZVAR ≡ v`
holds by kernel conversion.

---

### Operational Semantics (BKV §3)

**BKV describe:** A big-step evaluation relation
`Ev : CExp τ → CValue τ → Prop` (notation `e ⇓ v`) with 9 rules:
e_Val, e_Op, e_Gt, e_Fst, e_Snd, e_App, e_Let, e_IfTrue, e_IfFalse.
BKV note: "the operational semantics can be presented very directly"
with intrinsic typing. BKV use `ble_nat` for the greater-than
comparison and destructure `TFIX e` directly in the application rule.

**rocq-domain-theory:** `lang/PCF_Operational.v` (332 lines) has the
same 9 evaluation rules with cosmetic differences:

| BKV description | Our implementation | Notes |
|-----------------|-------------------|-------|
| `Ev` relation | `Eval` | Renamed |
| `ble_nat n2 n1` | `n₂ <? n₁` (`Nat.ltb`) | Stdlib modernization |
| `e_App` destructures `TFIX e` | `e_App` takes `FIX τ₁ τ₂ body` | More explicit pattern |

**What we add beyond BKV:**
- `Converges e := ∃ v, Eval e v` with `e ⇓` notation
- `eval_deterministic`: the evaluation relation is functional
- Inversion lemmas: `eval_let_inv`, `eval_app_fix_inv`, `eval_ifb_inv`

---

### Denotational Semantics (BKV §3.1)

**BKV describe:** Type interpretations `SemTy`, environment
interpretations `SemEnv`, and mutually recursive denotation functions
`SemVal`/`SemExp` defined by structural recursion on terms. Each case
is a point-free composition of library combinators. BKV use setoid
equality `==` and the coinductive lift monad. They describe a
substitution lemma (`SemCommutesWithSubst`) stating that denotation
commutes with syntactic substitution.

**rocq-domain-theory:** `lang/PCF_Denotational.v` (1167 lines) follows
the same point-free design:

| BKV description | Our implementation | Notes |
|-----------------|-------------------|-------|
| `SemTy`/`SemEnv` | `sem_ty`/`sem_env` | Snake_case |
| `SemVal`/`SemExp` | `sem_val`/`sem_exp` | |
| `SemSubst` | `sem_subst` | |
| `SemCommutesWithSubst` | `sem_val_subst` + `sem_exp_subst` | Split into two lemmas |
| `SimpleOp2 op` | `nat_binop op` | More descriptive name |
| `choose @3 (...)` (curried conditional) | `cont_ifb ∘ ⟨sem_val v, ⟨sem_exp e₁, sem_exp e₂⟩⟩` | Explicit pairing |
| `Kleislir` | `kleislir` | Same concept |
| `FIXP ∘ curry(curry(SemExp e))` | `FIXP ∘ flip(curry(flip(curry(sem_exp body))))` | Double flip for binding order |
| Setoid `==` | Leibniz `=` | See DD-004 |
| Coinductive `(SemTy τ)⊥` | `option (sem_ty τ)` | Flat lift |

**What we add beyond BKV:**

- **Renaming route** (see DD-012): The substitution lemma is proved via
  an explicit renaming chain: `sem_ren_ext` → `sem_val_ren`/`sem_exp_ren`
  → `sem_ren_wk` → `sem_val_wk` → `sem_subst_ext` → `sem_val_subst`/
  `sem_exp_subst`. BKV describe the bootstrapping strategy in prose but
  do not detail the proof structure.

- **Computation lemmas**: `sem_val_NLIT`, `sem_val_BLIT`, `sem_val_PAIR`,
  `sem_val_FIX_unfold`, `sem_exp_VAL`, `sem_exp_LET`, `sem_exp_APP`,
  `sem_exp_FST`, `sem_exp_SND`, `sem_exp_OP`, `sem_exp_GT`,
  `sem_exp_IFB`, `sem_exp_IFB_true`, `sem_exp_IFB_false`.

- **Notation**: `⟦v⟧ᵥ`, `⟦e⟧ₑ`, `⟦v⟧ᶜᵥ`, `⟦e⟧ᶜₑ` for denotation.

---

### Soundness (BKV §3.2)

**BKV describe:** The soundness theorem
`e ⇓ v → SemExp e == η ∘ SemVal v` (point-free, setoid equality).
The proof is by induction on the evaluation derivation.

**rocq-domain-theory:** `lang/PCF_Soundness.v` (261 lines).

| BKV description | Our implementation | Notes |
|-----------------|-------------------|-------|
| `SemExp e == η ∘ SemVal v` (point-free, setoid) | `sem_exp e tt = Some (sem_val v tt)` (pointwise, Leibniz) | Closed-term form |
| Stated for open terms | Stated for closed terms | Sufficient for adequacy |
| Induction on `Ev` | Induction on `Eval` | Same strategy |

**What we add beyond BKV:**
- `soundness_not_none`: convergence implies non-⊥ denotation
- `soundness_val`: values denote themselves
- `soundness_denotation_agree`: co-evaluating terms have equal denotations

---

### Adequacy (BKV §3.2)

**BKV describe:** The adequacy theorem
`SemExp e ≠ ⊥ → Converges e`. They describe the proof via a logical
relation (type-indexed family of relations between denotations and
syntactic terms) but note: "The proof is somewhat involved." BKV describe
the logical relation, the fundamental lemma by mutual induction on
syntax, and the derivation of adequacy as a corollary.

**rocq-domain-theory:** `lang/PCF_Adequacy.v` (820 lines) fully
formalizes the proof following BKV's described strategy.

| BKV description | Our implementation | Notes |
|-----------------|-------------------|-------|
| `SemExp e ≠ ⊥` | `sem_exp e tt <> None` | Flat lift |
| `Converges e` | `e ⇓` := `∃ v, e ⇓ v` | |
| Logical relation described in prose | `rel_val`/`rel_exp` by `Fixpoint` on `Ty` | Fully formalized |
| Fundamental lemma | `fundamental_lemma` via `Combined Scheme val_exp_ind` | Mutual induction |
| FIX case "uses Scott induction" | `fixp_ind` applied with admissibility proof | |

**What we add beyond BKV:**

- `rel_val_admissible` / `rel_exp_admissible`: admissibility proofs by
  induction on `Ty`, using chain-stabilisation properties of the lift
  CPO and `eval_deterministic`.
- `rel_env`: environment relation (semantic environment related to
  syntactic substitution).
- `convergence_iff_defined`: the full correspondence
  `e ⇓ ↔ sem_exp e tt <> None`, combining soundness and adequacy.

**Key proof techniques:**
- FIX case uses `fixp_ind` with nested natural-number induction.
- Arrow case in `rel_val_admissible` uses `Eqdep.EqdepTheory.inj_pair2`
  to invert dependent pairs.
- Imports `Classical` for `excluded_middle` in chain case analysis.

---

## New Contributions Beyond BKV

The following components have no counterpart in BKV's paper.

---

### CPO-Enriched Categories

BKV implicitly use the fact that CPO is self-enriched (composition of
continuous functions is continuous). We make this explicit:

- `structures/Enriched.v` (378 lines): `CPOEnrichedCat` HB structure
  with hom-CPOs, continuous composition, locally continuous functors.
- `instances/Function.v` (436 lines): Registers `CPO.type` as a
  `CPOEnrichedCat` instance with `cont_fun` as hom-CPOs.
- `theory/EnrichedTheory.v` (706 lines): Joint continuity of
  composition, `lc_functor` record, EP-pair infrastructure.

---

### Natural Transformations and Yoneda

- `theory/NatTrans.v` (518 lines): Enriched natural transformations
  between locally continuous endofunctors. Pointwise order, chains,
  suprema — natural transformations form a CPO. Identity, vertical
  composition, left/right whiskering, interchange law.

- `instances/Yoneda.v` (443 lines): Representable functor `Hom(X,-)`,
  enriched Yoneda lemma with both directions and round-trip laws,
  packaged as an `ep_pair`.

Reference: Kelly (1982), Mac Lane (1998).

---

### Scott Topology

- `theory/ScottTopology.v` (~520 lines): Way-below relation `x ≪ y`,
  Scott-open sets, the Scott topology on CPOs, and basic properties.

Reference: A&J §2.1.1.

---

### Quantum Domain Theory

Not present in BKV. Based on KLM (2024):

- `quantum/QuantumStructure.v` (~340 lines): Involutive quantales,
  quantum posets, Kronecker delta.
- `quantum/qCPO.v` (~390 lines): Quantum chains, convergence, quantum
  CPO property, quantum Scott continuity.
- `quantum/qCPOProperties.v` (~1022 lines): Bundled continuous maps,
  category laws, cofinal subsequences, hom-set CPO-enrichment, quantum
  Kleene fixed-point theorem.

---

## Axiom Comparison

**BKV:** The paper describes all constructions but, being a paper, does
not distinguish between "proved" and "axiomatic" in the Coq sense.
The paper presents suprema for function spaces, sums, and the lift as
existing constructions without detailed proofs.

**rocq-domain-theory:** All domain-theoretic suprema are fully proved.

| Construction | Status |
|-------------|--------|
| Function-space sup | Proved constructively (`theory/FunctionSpaces.v`) |
| Sum sup | Proved constructively (`theory/Sums.v`) |
| Lift sup | Proved via `ClassicalEpsilon` (`theory/Lift.v`) |
| Bilimit existence | `Axiom bilimit_exists` (requires omega-product CPO) |

**Classical axioms used:**
- `ClassicalEpsilon` in `Lift.v` (for `excluded_middle_informative` and
  `constructive_indefinite_description`)
- `Classical` in `PCF_Adequacy.v` and `ScottTopology.v`
- `ProofIrrelevance` in `Morphisms.v` (for `cont_comp_assoc`)
- `FunctionalExtensionality` in `PCF_Denotational.v` and
  `qCPOProperties.v`

**Admitted results:** `theory/LiftMonad.v` (supplementary coinductive
file only) has two admitted lemmas (`bisim_trans`, `converges_bisim`)
due to Rocq's productivity checker limitations. Neither is used
downstream. See DD-007.

---

## API Reference

### Naming Conventions

BKV use CamelCase and `T`-prefixed constructors. We use snake_case for
definitions and ALLCAPS for syntactic constructors (without the `T`
prefix).

| BKV paper | Our code | Category |
|-----------|----------|----------|
| `SemTy`, `SemEnv`, `SemVal`, `SemExp` | `sem_ty`, `sem_env`, `sem_val`, `sem_exp` | Denotation |
| `TINT`, `TBOOL`, `TVAR`, `TFIX` | `NLIT`, `BLIT`, `VAR`, `FIX` | Syntax |
| `TVAL`, `TLET`, `TAPP` | `VAL`, `LET`, `APP` | Syntax |
| `singleSubst`, `doubleSubst` | `single_subst`, `double_subst` | Substitution |
| `SemCommutesWithSubst` | `sem_val_subst` / `sem_exp_subst` | Lemmas |
| `fconti` | `cont_fun` | Structures |
| `lub_of_chain` | `sup` (`⊔ c`) | CPO |
| `lub_upper` / `lub_least` | `sup_upper` / `sup_least` | CPO |
| `fixp`, `FIXP` | `fixp`, `FIXP` | Fixed points (same) |
| `fixp_ind` | `fixp_ind` | Fixed points (same) |

### Module Imports

```coq
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Theory Require Import OrderTheory CPOTheory FixedPoints
  Products Sums FunctionSpaces Lift ScottTopology ChainTheory
  EnrichedTheory NatTrans DomainEquations.
From DomainTheory.Instances Require Import Discrete Nat Function Yoneda FunLift.
From DomainTheory.Lang Require Import PCF_Syntax PCF_Operational
  PCF_Denotational PCF_Soundness PCF_Adequacy.
From DomainTheory.Quantum Require Import QuantumStructure qCPO qCPOProperties.
```

---

## What We Preserve from BKV

The following design choices from BKV are adopted unchanged:

- **Intrinsic typing** for PCF: well-typedness by construction
- **ANF**: arguments to function calls must be values
- **Typed de Bruijn indices** via `Var Γ τ`
- **Renaming bootstrap**: renamings first, then substitutions
- **Big-step CBV evaluation** with 9 rules
- **Point-free denotational semantics**: each case is a composition of
  library combinators
- **Soundness by induction on evaluation**
- **Adequacy via logical relation** with fundamental lemma

- **`chain` as a record** (not an HB structure)
- **`mono_fun` as a record** with coercion to the underlying function
- **Separating strict from continuous**: strictness not always required
- **`c.[n]` notation** for chain access
- **Diagrammatic composition**: `g ∘ f` meaning "first f, then g"
