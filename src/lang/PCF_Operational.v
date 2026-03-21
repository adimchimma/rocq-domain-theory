(*  PCF_Operational

    Phase 1: Big-step call-by-value evaluation for PCFv.

    This is [src/lang/PCF_Operational.v].

    Imports:
      [src/lang/PCF_Syntax.v] — Ty, Env, Value, Exp, CValue, CExp,
                                 singleSubstExp, doubleSubstExp

    Summary
    =======
    We define the big-step evaluation relation [e ⇓ v] for closed PCFv
    terms, following Benton-Kennedy-Varming §3.  The relation is in [Prop]: since
    our terms are intrinsically typed, we never need to extract information
    from a derivation; the derivation is used only as a proof object in
    soundness and adequacy arguments.

    The language is call-by-value in ANF, so:
      - every argument to a function call is already a value,
      - [LET] is the only sequencing construct,
      - [FIX] is the only source of divergence.

    Because our syntax is intrinsically typed and uses de Bruijn indices,
    the evaluation rules for APP and LET use the substitution operations
    [doubleSubstExp] and [singleSubstExp] from [PCF_Syntax.v] directly;
    there is no separate notion of "substituting a named variable".

    Contents:
    - §1  The evaluation relation [Eval] and notation [e ⇓ v]
    - §2  Convergence: [Converges e]
    - §3  Derived lemmas: determinism and inversion

    Phase coverage:
      Phase 1 — all sections
      Used by [PCF_Soundness.v] (induction on [⇓]),
               [PCF_Adequacy.v] (logical relation over [⇓])

    References:
      Benton, Kennedy & Varming (2009) §3 (typed language, big-step)
*)

From Stdlib Require Import List PeanoNat Bool Program.Equality.
From DomainTheory.Lang Require Import PCF_Syntax.

Import ListNotations.


(* ================================================================== *)
(*   §1  The evaluation relation                                       *)
(* ================================================================== *)
(*
    [Eval e v] (written [e ⇓ v]) is a big-step CBV evaluation relation
    on _closed_ terms.  The inductive is in [Prop].

    Rules:

      e_Val:
        ────────
        VAL v ⇓ v

      e_Let:
        e₁ ⇓ v₁     e₂[v₁/0] ⇓ v₂
        ────────────────────────────
        LET e₁ e₂ ⇓ v₂

      e_App:
        body[varg/0, FIX.../1] ⇓ v
        ──────────────────────────────────
        APP (FIX τ₁ τ₂ body) varg ⇓ v

      e_Fst:
        ──────────────────────
        FST (PAIR v₁ v₂) ⇓ v₁

      e_Snd:
        ──────────────────────
        SND (PAIR v₁ v₂) ⇓ v₂

      e_Op:
        ──────────────────────────────────────────
        OP op (NLIT n₁) (NLIT n₂) ⇓ NLIT (op n₁ n₂)

      e_Gt:
        ──────────────────────────────────────────────────────
        GT (NLIT n₁) (NLIT n₂) ⇓ BLIT (n₂ <? n₁)

      e_IfTrue:
        e₁ ⇓ v
        ──────────────────────────────
        IFB (BLIT true) e₁ e₂ ⇓ v

      e_IfFalse:
        e₂ ⇓ v
        ──────────────────────────────
        IFB (BLIT false) e₁ e₂ ⇓ v

    Notes:

    [e_App]: the only closed value of function type is [FIX τ₁ τ₂ body],
    since [VAR] requires a non-empty context.  The substitution
    [doubleSubstExp varg (FIX τ₁ τ₂ body) body] replaces:
      - index 0 (ZVAR) with [varg], the argument
      - index 1 (SVAR ZVAR) with [FIX τ₁ τ₂ body], the function itself
    This is exactly the unrolling of one step of general recursion.

    [e_Fst / e_Snd]: similarly, the only closed value of product type is
    [PAIR v₁ v₂].  No additional evaluation is needed on [v₁] or [v₂]
    because they are already values.

    [e_Gt]: we encode [n₁ > n₂] as the boolean [n₂ <? n₁] using
    [Nat.ltb] from the Stdlib.  The notation [<?] is defined there.
*)

Inductive Eval : forall {τ : Ty}, CExp τ -> CValue τ -> Prop :=

  (*  A value expression evaluates to its value.  *)
  | e_Val : forall {τ} (v : CValue τ),
      Eval (VAL v) v

  (*  Sequential composition: evaluate e₁ to v₁, then e₂ with v₁
      substituted for the bound variable.  *)
  | e_Let : forall {τ₁ τ₂}
      (e₁ : CExp τ₁) (v₁ : CValue τ₁)
      (e₂ : Exp [τ₁] τ₂) (v₂ : CValue τ₂),
      Eval e₁ v₁ ->
      Eval (singleSubstExp v₁ e₂) v₂ ->
      Eval (LET e₁ e₂) v₂

  (*  Function application: unroll one step of the fixpoint.
      [doubleSubstExp varg (FIX τ₁ τ₂ body) body] substitutes
        index 0 ↦ varg             (the argument)
        index 1 ↦ FIX τ₁ τ₂ body  (the recursive self-reference)  *)
  | e_App : forall {τ₁ τ₂}
      (body : Exp [τ₁ ; τ₁ →ₜ τ₂] τ₂)
      (varg : CValue τ₁)
      (v : CValue τ₂),
      Eval (doubleSubstExp varg (FIX τ₁ τ₂ body) body) v ->
      Eval (APP (FIX τ₁ τ₂ body) varg) v

  (*  First projection of a pair.  *)
  | e_Fst : forall {τ₁ τ₂}
      (v₁ : CValue τ₁) (v₂ : CValue τ₂),
      Eval (FST (PAIR v₁ v₂)) v₁

  (*  Second projection of a pair.  *)
  | e_Snd : forall {τ₁ τ₂}
      (v₁ : CValue τ₁) (v₂ : CValue τ₂),
      Eval (SND (PAIR v₁ v₂)) v₂

  (*  Binary arithmetic: apply the Coq function [op] to the two nat
      literals.  This handles add, mul, sub, etc. uniformly.  *)
  | e_Op : forall (op : nat -> nat -> nat) (n₁ n₂ : nat),
      Eval (OP op (NLIT n₁) (NLIT n₂)) (NLIT (op n₁ n₂))

  (*  Comparison: [GT (NLIT n₁) (NLIT n₂)] evaluates to [BLIT true]
      if [n₁ > n₂] and to [BLIT false] otherwise.
      We express [n₁ > n₂] as the boolean [n₂ <? n₁].  *)
  | e_Gt : forall (n₁ n₂ : nat),
      Eval (GT (NLIT n₁) (NLIT n₂)) (BLIT (n₂ <? n₁))

  (*  Conditional: true branch.  *)
  | e_IfTrue : forall {τ}
      (e₁ e₂ : CExp τ) (v : CValue τ),
      Eval e₁ v ->
      Eval (IFB (BLIT true) e₁ e₂) v

  (*  Conditional: false branch.  *)
  | e_IfFalse : forall {τ}
      (e₁ e₂ : CExp τ) (v : CValue τ),
      Eval e₂ v ->
      Eval (IFB (BLIT false) e₁ e₂) v.

(*  The evaluation relation as an infix notation.  *)
Notation "e ⇓ v" := (Eval e v) (at level 70, no associativity).


(* ================================================================== *)
(*   §2  Convergence                                                   *)
(* ================================================================== *)
(*
    [Converges e] asserts that [e] evaluates to _some_ value; it is the
    propositional existential shadow of [Eval].

    This is the predicate used in the statement of adequacy:
        ⟦e⟧ ≠ ⊥  →  Converges e
*)

Definition Converges {τ : Ty} (e : CExp τ) : Prop :=
  exists (v : CValue τ), e ⇓ v.

Notation "e ⇓" := (Converges e) (at level 70, no associativity).

(*  Every value-expression converges.  *)
Lemma val_converges {τ} (v : CValue τ) : (VAL v) ⇓.
Proof.
  exists v. exact (e_Val v).
Qed.

(*  If [e ⇓ v] then [e] converges.  *)
Lemma eval_converges {τ} (e : CExp τ) (v : CValue τ) : e ⇓ v -> e ⇓.
Proof.
  intro H. exists v. exact H.
Qed.


(* ================================================================== *)
(*   §3  Derived lemmas                                               *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(*   Determinism                                                       *)
(* ------------------------------------------------------------------ *)
(*
    The relation [⇓] is deterministic: a closed expression evaluates to
    at most one value.  The proof is a straightforward double induction
    on the two derivations.

    This is used in [PCF_Soundness.v] to justify rewriting [⟦e⟧] along
    both the first and second evaluation derivation simultaneously.
*)

Theorem eval_deterministic :
  forall {τ} (e : CExp τ) (v₁ v₂ : CValue τ),
    e ⇓ v₁ -> e ⇓ v₂ -> v₁ = v₂.
Proof.
  intros τ e v₁ v₂ H1.
  revert v₂.
  induction H1 as
    [ τ v
    | τ₁ τ₂ e₁ w₁ e₂ w₂ He₁ IH₁ He₂ IH₂
    | τ₁ τ₂ body varg w He IH
    | τ₁ τ₂ v₁ v₂
    | τ₁ τ₂ v₁ v₂
    | op n₁ n₂
    | n₁ n₂
    | τ e₁ e₂ w He IH
    | τ e₁ e₂ w He IH
    ]; intros v₃ H2.
  
    (*  e_Val  *)
  - dependent destruction H2; reflexivity.

  (*  e_Let  *)
  - dependent destruction H2.
    apply IH₂.
    rewrite (IH₁ _ H2_).
    exact H2_0.

  (*  e_App  *)
  - dependent destruction H2.
    exact (IH _ H2).

  (*  e_Fst  *)
  - dependent destruction H2; reflexivity.

  (*  e_Snd  *)
  - dependent destruction H2; reflexivity.

  (*  e_Op  *)
  - dependent destruction H2; reflexivity.

  (*  e_Gt  *)
  - dependent destruction H2; reflexivity.

  (*  e_IfTrue  *)
  - dependent destruction H2. exact (IH _ H2).

  (*  e_IfFalse  *)
  - dependent destruction H2. exact (IH _ H2).
Qed.

(* ------------------------------------------------------------------ *)
(*   Inversion lemmas                                                  *)
(* ------------------------------------------------------------------ *)
(*
    These lemmas expose the structure of a derivation given information
    about the head constructor of the expression.  They are stated in
    the forward direction (as eliminators) and used in soundness proofs
    where we need to case-split on what rule produced a given derivation.

    We provide inversion for the constructs whose evaluation rules require
    the most bookkeeping: [LET], [APP], and [IFB].  For the others
    ([VAL], [FST], [SND], [OP], [GT]), Rocq's built-in [inversion]
    tactic is both sufficient and efficient.
*)

(*
    If [LET e₁ e₂ ⇓ v₂] then there exists an intermediate value [v₁]
    such that [e₁ ⇓ v₁] and [e₂[v₁/0] ⇓ v₂].
*)
Lemma eval_let_inv {τ₁ τ₂}
    (e₁ : CExp τ₁) (e₂ : Exp [τ₁] τ₂) (v₂ : CValue τ₂) :
    LET e₁ e₂ ⇓ v₂ ->
    exists (v₁ : CValue τ₁),
      e₁ ⇓ v₁ /\ singleSubstExp v₁ e₂ ⇓ v₂.
Proof.
  intro H. dependent destruction H.
  exists v₁.
  exact (conj H H0).
Qed.

(*
    If [APP (FIX τ₁ τ₂ body) varg ⇓ v] then the unrolled body
    evaluates to [v].
*)
Lemma eval_app_fix_inv {τ₁ τ₂}
    (body : Exp [τ₁ ; τ₁ →ₜ τ₂] τ₂)
    (varg : CValue τ₁) (v : CValue τ₂) :
    APP (FIX τ₁ τ₂ body) varg ⇓ v ->
    doubleSubstExp varg (FIX τ₁ τ₂ body) body ⇓ v.
Proof.
  intro H. dependent destruction H.
  exact H.
Qed.

(*
    If [IFB (BLIT b) e₁ e₂ ⇓ v] then either [b = true] and [e₁ ⇓ v],
    or [b = false] and [e₂ ⇓ v].
*)
Lemma eval_ifb_inv {τ} (b : bool)
    (e₁ e₂ : CExp τ) (v : CValue τ) :
    IFB (BLIT b) e₁ e₂ ⇓ v ->
    (b = true  /\ e₁ ⇓ v) \/
    (b = false /\ e₂ ⇓ v).
Proof.
  intro H.
  destruct b.
  - left. dependent destruction H.
    exact (conj eq_refl H).
  - right. dependent destruction H.
    exact (conj eq_refl H).
Qed.