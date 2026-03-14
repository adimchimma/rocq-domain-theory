(*  PCFTests

    Unit tests for the PCF formalisation: syntax, substitution,
    denotational semantics computation rules, and soundness.

    Tests:
    - §1  Substitution — single_subst and double_subst computation
    - §2  Denotational computation — sem_val / sem_exp rules
    - §3  Soundness — e ⇓ v implies denotation agreement
    - §4  Adequacy — convergence iff denotation ≠ None
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order Morphisms.
From DomainTheory.Lang Require Import
     PCF_Syntax
     PCF_Operational
     PCF_Denotational
     PCF_Soundness
     PCF_Adequacy.


(* ================================================================== *)
(* §1  Substitution — definitional computation via var_case            *)
(* ================================================================== *)
(*
    Because single_subst and double_subst are defined via [var_case],
    these hold definitionally (by reflexivity).
*)

Section SubstTests.

(* single_subst v ZVAR = v. *)
Lemma test_single_subst_zero :
    forall (v : CValue Nat),
    single_subst v Nat ZVAR = v.
Proof. intro. reflexivity. Qed.

(* double_subst varg vfun ZVAR = varg. *)
Lemma test_double_subst_zero :
    forall (varg : CValue Nat) (vfun : CValue (Nat →ₜ Nat)),
    double_subst varg vfun Nat ZVAR = varg.
Proof. intros. reflexivity. Qed.

(* double_subst varg vfun (SVAR ZVAR) = vfun. *)
Lemma test_double_subst_one :
    forall (varg : CValue Nat) (vfun : CValue (Nat →ₜ Nat)),
    double_subst varg vfun (Nat →ₜ Nat) (SVAR ZVAR) = vfun.
Proof. intros. reflexivity. Qed.

End SubstTests.


(* ================================================================== *)
(* §2  Denotational computation — sem_val / sem_exp rules              *)
(* ================================================================== *)

Section DenotationalTests.

(* sem_cval (NLIT n) = n. *)
Lemma test_sem_val_NLIT :
    ⟦ NLIT 42 ⟧ᶜᵥ = 42.
Proof. unfold sem_cval. rewrite sem_val_NLIT. reflexivity. Qed.

(* sem_cval (BLIT b) = b. *)
Lemma test_sem_val_BLIT :
    ⟦ BLIT true ⟧ᶜᵥ = true.
Proof. unfold sem_cval. rewrite sem_val_BLIT. reflexivity. Qed.

(* sem_cval (PAIR v1 v2) = (sem_cval v1, sem_cval v2). *)
Lemma test_sem_val_PAIR :
    ⟦ PAIR (NLIT 1) (BLIT false) ⟧ᶜᵥ = (1, false).
Proof.
  unfold sem_cval. rewrite sem_val_PAIR.
  rewrite sem_val_NLIT. rewrite sem_val_BLIT. reflexivity.
Qed.

(* sem_exp (VAL v) applies ret. *)
Lemma test_sem_exp_VAL :
    ⟦ VAL (NLIT 42) ⟧ᶜₑ = Some 42.
Proof.
  unfold sem_cexp.
  rewrite sem_exp_VAL.
  rewrite cont_comp_apply.
  rewrite sem_val_NLIT.
  simpl.
  reflexivity.
Qed.

(* sem_exp (OP Nat.add ...) computes the sum. *)
Lemma test_sem_exp_OP :
    ⟦ OP Nat.add (NLIT 3) (NLIT 4) ⟧ᶜₑ = Some 7.
Proof.
  unfold sem_cexp.
  rewrite sem_exp_OP.
  repeat rewrite sem_val_NLIT. reflexivity.
Qed.

(* sem_exp (GT ...) computes the comparison. *)
Lemma test_sem_exp_GT :
    ⟦ GT (NLIT 5) (NLIT 3) ⟧ᶜₑ = Some true.
Proof.
  unfold sem_cexp.
  rewrite sem_exp_GT. 
  repeat rewrite sem_val_NLIT. reflexivity.
Qed.

(* sem_exp (FST ...) projects. *)
Lemma test_sem_exp_FST :
    ⟦ FST (PAIR (NLIT 1) (BLIT true)) ⟧ᶜₑ = Some 1.
Proof.
  unfold sem_cexp.
  rewrite sem_exp_FST.
  reflexivity.
Qed.

(* sem_exp (SND ...) projects. *)
Lemma test_sem_exp_SND :
    ⟦ SND (PAIR (NLIT 1) (BLIT true)) ⟧ᶜₑ = Some true.
Proof.
  unfold sem_cexp.
  rewrite sem_exp_SND.
  reflexivity.
Qed.

(* sem_exp (IFB true ...) selects the true branch. *)
Lemma test_sem_exp_IFB_true :
    ⟦ IFB (BLIT true) (VAL (NLIT 1)) (VAL (NLIT 0)) ⟧ᶜₑ = Some 1.
Proof.
  unfold sem_cexp.
  rewrite sem_exp_IFB_true; reflexivity. 
Qed.

(* sem_exp (IFB false ...) selects the false branch. *)
Lemma test_sem_exp_IFB_false :
    ⟦ IFB (BLIT false) (VAL (NLIT 1)) (VAL (NLIT 0)) ⟧ᶜₑ = Some 0.
Proof.
  unfold sem_cexp.
  rewrite sem_exp_IFB_false; reflexivity.
Qed.

End DenotationalTests.


(* ================================================================== *)
(* §3  Soundness — operational ⇓ implies denotation agreement         *)
(* ================================================================== *)

Section SoundnessTests.

(*
    The identity function: FIX Nat Nat (VAL (VAR ZVAR))
    Operationally:  APP pcf_id (NLIT 5) ⇓ NLIT 5
    Soundness:      ⟦ APP pcf_id (NLIT 5) ⟧ᶜₑ = Some ⟦ NLIT 5 ⟧ᶜᵥ
*)
Definition pcf_id : CValue (Nat →ₜ Nat) :=
  FIX Nat Nat (VAL (VAR ZVAR)).

Lemma test_eval_id : APP pcf_id (NLIT 5) ⇓ NLIT 5.
Proof.
  apply e_App. simpl. apply e_Val.
Qed.

Lemma test_sound_id :
    ⟦ APP pcf_id (NLIT 5) ⟧ᶜₑ = Some ⟦ NLIT 5 ⟧ᶜᵥ.
Proof. exact (soundness _ _ test_eval_id). Qed.

(*
    Addition: OP Nat.add (NLIT 3) (NLIT 4) ⇓ NLIT 7.
*)
Lemma test_eval_add : OP Nat.add (NLIT 3) (NLIT 4) ⇓ NLIT 7.
Proof. apply e_Op. Qed.

Lemma test_sound_add :
    ⟦ OP Nat.add (NLIT 3) (NLIT 4) ⟧ᶜₑ = Some ⟦ NLIT 7 ⟧ᶜᵥ.
Proof. exact (soundness _ _ test_eval_add). Qed.

(* Values always have denotation Some. *)
Lemma test_soundness_val :
    forall (v : CValue Nat),
    ⟦ VAL v ⟧ᶜₑ = Some ⟦ v ⟧ᶜᵥ.
Proof. intro. exact (soundness_val v). Qed.

(* If e ⇓ then its denotation is not None. *)
Lemma test_soundness_not_none :
    forall (e : CExp Nat), e ⇓ -> ⟦ e ⟧ᶜₑ <> None.
Proof.
  intros e [v Hv].
  exact (soundness_not_none e (ex_intro _ v Hv)).
Qed.

(* Determinism: e ⇓ v₁ and e ⇓ v₂ imply sem_val v₁ = sem_val v₂. *)
Lemma test_denotation_agree :
    forall (e : CExp Nat) (v₁ v₂ : CValue Nat),
    e ⇓ v₁ -> e ⇓ v₂ ->
    ⟦ v₁ ⟧ᶜᵥ = ⟦ v₂ ⟧ᶜᵥ.
Proof.
  intros. exact (soundness_denotation_agree e v₁ v₂ H H0).
Qed.

End SoundnessTests.


(* ================================================================== *)
(* §4  Adequacy — convergence iff denotation ≠ None                   *)
(* ================================================================== *)

Section AdequacyTests.

(* Forward direction: e ⇓ -> denotation ≠ None. *)
Lemma test_converges_implies_defined :
    (OP Nat.add (NLIT 3) (NLIT 4)) ⇓ ->
    ⟦ OP Nat.add (NLIT 3) (NLIT 4) ⟧ᶜₑ <> None.
Proof.
  intro H. exact (convergence_implies_defined _ H).
Qed.

(* Backward direction: denotation ≠ None -> e ⇓. *)
Lemma test_defined_implies_converges :
    ⟦ OP Nat.add (NLIT 3) (NLIT 4) ⟧ᶜₑ <> None ->
    (OP Nat.add (NLIT 3) (NLIT 4)) ⇓.
Proof.
  intro H. exact (proj2 (convergence_iff_defined _) H).
Qed.

(* Full iff. *)
Lemma test_convergence_iff :
    (OP Nat.add (NLIT 3) (NLIT 4)) ⇓ <->
    ⟦ OP Nat.add (NLIT 3) (NLIT 4) ⟧ᶜₑ <> None.
Proof. exact (convergence_iff_defined _). Qed.

(* Concrete convergence via adequacy:
   denotation is Some 7 ≠ None, so the term converges. *)
Lemma test_adequate_add :
    (OP Nat.add (NLIT 3) (NLIT 4)) ⇓.
Proof.
  apply (proj2 (convergence_iff_defined _)).
  simpl.
  discriminate.
Qed.

End AdequacyTests.
