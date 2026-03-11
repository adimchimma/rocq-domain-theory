(*  PCF_Soundness

    Phase 1: Computational soundness of PCF denotational semantics.

    This is [src/lang/PCF_Soundness.v].

    Imports:
      [src/lang/PCF_Syntax.v]        — Ty, Env, Value, Exp, CValue, CExp,
                                        singleSubstExp, doubleSubstExp
      [src/lang/PCF_Operational.v]   — Eval (e ⇓ v), Converges
      [src/lang/PCF_Denotational.v]  — sem_ty, sem_env, sem_val, sem_exp,
                                        sem_cval, sem_cexp,
                                        sem_val_FIX_unfold,
                                        sem_subst_single, sem_subst_double,
                                        sem_val_subst, sem_exp_subst,
                                        sem_exp_VAL, sem_exp_LET,
                                        sem_exp_APP, sem_exp_FST,
                                        sem_exp_SND, sem_exp_OP,
                                        sem_exp_GT, sem_exp_IFB_true,
                                        sem_exp_IFB_false

    Summary
    =======
    We prove that the denotational semantics is *sound* with respect to
    the big-step operational semantics:

        Theorem soundness :
          forall τ (e : CExp τ) (v : CValue τ),
            e ⇓ v  ->  sem_exp e tt = Some (sem_val v tt).

    In words: if a closed expression evaluates to a closed value, then
    the denotation of the expression equals [Some] applied to the
    denotation of the value.  The lift monad [option] carries partiality;
    [None] denotes divergence.  Soundness says that convergence in the
    operational semantics implies non-divergence in the denotation.

    Proof strategy
    ==============
    By structural induction on the derivation [H : e ⇓ v].  Each rule
    of the big-step semantics corresponds to one case; most close by
    rewriting with the β-computation rules exported from
    [PCF_Denotational.v] plus the induction hypothesis.

    The two non-trivial cases are:

      e_Let  (sequencing):
        We have [e₁ ⇓ w₁] and [singleSubstExp w₁ e₂ ⇓ w₂].
        The β-rule [sem_exp_LET] unfolds [sem_exp (LET e₁ e₂) tt] to a
        match on [sem_exp e₁ tt].  By IH₁ that equals
        [Some (sem_val w₁ tt)], so the match reduces.  We then use
        [sem_exp_subst] and [sem_subst_single] to rewrite the goal from
        [sem_exp e₂ (sem_val w₁ tt, tt)] to
        [sem_exp (singleSubstExp w₁ e₂) tt], and IH₂ closes.

      e_App  (function application):
        We have [doubleSubstExp varg (FIX τ₁ τ₂ body) body ⇓ w].
        The β-rule [sem_exp_APP] gives:
            sem_exp (APP (FIX τ₁ τ₂ body) varg) tt
              = sem_val (FIX τ₁ τ₂ body) tt (sem_val varg tt).
        [sem_val_FIX_unfold] rewrites the RHS to:
            sem_exp body (sem_val varg tt,
                         (sem_val (FIX τ₁ τ₂ body) tt, tt)).
        [sem_exp_subst] and [sem_subst_double] then rewrite this to:
            sem_exp (doubleSubstExp varg (FIX τ₁ τ₂ body) body) tt,
        and IH closes the goal.

    Contents:
    - §1  Substitution interface lemmas
    - §2  Main soundness theorem
    - §3  Corollaries

    Phase coverage:
      Phase 1 — all sections.
      Used by [PCF_Adequacy.v].

    References:
      Benton, Kennedy, Varming — "Some Domain Theory and Denotational
        Semantics in Coq", §3.2, Theorem [Soundness].
*)

From Stdlib Require Import List PeanoNat Bool Program.Equality.
From DomainTheory.Structures Require Import Order Morphisms.
From DomainTheory.Lang Require Import
  PCF_Syntax
  PCF_Operational
  PCF_Denotational.

Import ListNotations.
Local Open Scope type_scope.


(* ================================================================== *)
(*   §1  Substitution interface lemmas                                 *)
(* ================================================================== *)
(*
    These lemmas connect the syntactic substitution operations
    [singleSubstExp] and [doubleSubstExp] from [PCF_Syntax.v] with the
    semantic denotation from [PCF_Denotational.v].

    They are derived by composing:
      [sem_exp_subst]:    sem_exp (substExp σ e) γ'
                            = sem_exp e (sem_subst σ γ')
      [sem_subst_single]: sem_subst (single_subst v)
                            = cont_pair (sem_val v) (cont_id _)
      [sem_subst_double]: sem_subst (double_subst varg vfun)
                            = cont_pair (sem_val varg)
                                (cont_pair (sem_val vfun) (cont_id _))

    Both are stated at closed type (environment [tt : unit]) since the
    soundness theorem only concerns closed terms.
*)

Lemma sem_single_subst {τ₁ τ₂ : Ty}
    (v : CValue τ₁) (e : Exp [τ₁] τ₂) :
    sem_exp (singleSubstExp v e) tt =
      sem_exp e (sem_val v tt, tt).
Proof.
  unfold singleSubstExp.
  rewrite sem_exp_subst.
  reflexivity.
Qed.

Lemma sem_double_subst {τ₁ τ₂ : Ty}
    (varg : CValue τ₁)
    (body : Exp [τ₁ ; τ₁ →ₜ τ₂] τ₂) :
    sem_exp (doubleSubstExp varg (FIX τ₁ τ₂ body) body) tt =
      sem_exp body (sem_val varg tt, (sem_val (FIX τ₁ τ₂ body) tt, tt)).
Proof.
  unfold doubleSubstExp.
  rewrite sem_exp_subst.
  reflexivity.
Qed.


(* ================================================================== *)
(*   §2  Main soundness theorem                                        *)
(* ================================================================== *)
(*
    Soundness: operational evaluation implies semantic equality.

        e ⇓ v  ->  sem_exp e tt = Some (sem_val v tt)

    Proof: by induction on the derivation [H : e ⇓ v], one case per
    evaluation rule.
*)

Theorem soundness :
    forall {τ : Ty} (e : CExp τ) (v : CValue τ),
      e ⇓ v  ->  sem_exp e tt = Some (sem_val v tt).
Proof.
  intros τ e v H.
  induction H as
    [ τ' v'
    | τ₁ τ₂ e₁ w₁ e₂ w₂  He₁ IH₁  He₂ IH₂
    | τ₁ τ₂ body varg w  He IH
    | τ₁ τ₂ v₁ v₂
    | τ₁ τ₂ v₁ v₂
    | op n₁ n₂
    | n₁ n₂
    | τ' e₁ e₂ w  He IH
    | τ' e₁ e₂ w  He IH
    ].

  (* e_Val:  VAL v ⇓ v *)
  - reflexivity.

  (* e_Let:  LET e₁ e₂ ⇓ w₂ *)
  - rewrite sem_exp_LET, IH₁.
    rewrite <- IH₂.
    rewrite sem_single_subst.
    reflexivity.

  (* e_App:  APP (FIX body) varg ⇓ w *)
  - rewrite sem_exp_APP, sem_val_FIX_unfold.
    rewrite <- IH.
    rewrite sem_double_subst.
    reflexivity.

  (* e_Fst:  FST (PAIR v₁ v₂) ⇓ v₁ *)
  - rewrite sem_exp_FST, sem_val_PAIR. reflexivity.

  (* e_Snd:  SND (PAIR v₁ v₂) ⇓ v₂ *)
  - rewrite sem_exp_SND, sem_val_PAIR. reflexivity.

  (* e_Op:  OP op (NLIT n₁) (NLIT n₂) ⇓ NLIT (op n₁ n₂) *)
  - rewrite sem_exp_OP. reflexivity.

  (* e_Gt:  GT (NLIT n₁) (NLIT n₂) ⇓ BLIT (n₂ <? n₁) *)
  - rewrite sem_exp_GT. reflexivity.

  (* e_IfTrue:  IFB (BLIT true) e₁ e₂ ⇓ w *)
  - rewrite sem_exp_IFB. simpl.
    exact IH.

  (* e_IfFalse:  IFB (BLIT false) e₁ e₂ ⇓ w *)
  - rewrite sem_exp_IFB. simpl.
    exact IH.
Qed.


(* ================================================================== *)
(*   §3  Corollaries                                                   *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(*   Convergence implies non-⊥ denotation                             *)
(* ------------------------------------------------------------------ *)
(*
    If [e] converges then its denotation is [Some _], not [None].

    This is the "easy" direction of computational adequacy.  The harder
    direction — [sem_exp e tt <> None] implies [e ⇓] — is proved in
    [PCF_Adequacy.v] via a logical relation.
*)

Corollary soundness_not_none :
    forall {τ : Ty} (e : CExp τ),
      e ⇓  ->  sem_exp e tt <> None.
Proof.
  intros τ e [v Hv].
  rewrite (soundness e v Hv).
  discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*   Values denote themselves                                          *)
(* ------------------------------------------------------------------ *)
(*
    [VAL v ⇓ v] by [e_Val], so soundness immediately gives
    [sem_exp (VAL v) tt = Some (sem_val v tt)].  Stated separately for
    use as a clean interface by [PCF_Adequacy.v].
*)

Corollary soundness_val :
    forall {τ : Ty} (v : CValue τ),
      sem_exp (VAL v) tt = Some (sem_val v tt).
Proof.
  intros τ v.
  exact (soundness (VAL v) v (e_Val v)).
Qed.

(* ------------------------------------------------------------------ *)
(*   Denotations agree on co-evaluating terms                         *)
(* ------------------------------------------------------------------ *)
(*
    If [e ⇓ v₁] and [e ⇓ v₂] then [sem_val v₁ tt = sem_val v₂ tt].
    Follows from [soundness] and injectivity of [Some].
    ([eval_deterministic] gives the stronger propositional [v₁ = v₂].)
*)

Corollary soundness_denotation_agree :
    forall {τ : Ty} (e : CExp τ) (v₁ v₂ : CValue τ),
      e ⇓ v₁  ->  e ⇓ v₂  ->  sem_val v₁ tt = sem_val v₂ tt.
Proof.
  intros τ e v₁ v₂ H₁ H₂.
  assert (Heq : Some (sem_val v₁ tt) = Some (sem_val v₂ tt)).
  { rewrite <- (soundness e v₁ H₁).
    rewrite <- (soundness e v₂ H₂).
    reflexivity. }
  injection Heq; intro; assumption.
Qed.
