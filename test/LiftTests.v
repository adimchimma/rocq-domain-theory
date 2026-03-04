(*  LiftTests

    Unit tests for the flat-lift construction [D⊥] from
    [src/theory/Lift.v].

    Tests:
    - §1  lift_le — ordering of None/Some values
    - §2  lift_sup — supremum for all-None and stabilising-Some chains
    - §3  ret — correctness and continuity
    - §4  kleisli — computation rules and continuity
    - §5  Monad law — left unit (kleisli f ∘ ret = f)
*)

From HB Require Import structures.
From Stdlib Require Import ClassicalEpsilon.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory ChainTheory CPOTheory Lift.
From DomainTheory.Instances Require Import Nat.

From Stdlib Require Import Arith Lia.


(* ================================================================== *)
(* §1  lift_le — ordering of None and Some values                      *)
(* ================================================================== *)

Section LiftLeTests.

(* None is below every lifted value. *)
Lemma test_lift_le_none_below_none :
    (None : option nat_inf) ⊑ None.
Proof.
  exact I.
Qed.

Lemma test_lift_le_none_below_some :
    (None : option nat_inf) ⊑ Some (fin 3).
Proof.
  exact I.
Qed.

(* Some d is NOT below None. *)
Lemma test_lift_le_some_not_below_none :
    ~ (Some (fin 0) : option nat_inf) ⊑ None.
Proof.
  exact (lift_some_not_le_none (fin 0)).
Qed.

(* Some d ⊑ Some d' iff d ⊑ d'. *)
Lemma test_lift_le_some_some_iff (d d' : nat_inf) :
    (Some d : option nat_inf) ⊑ Some d' <-> d ⊑ d'.
Proof.
  exact (lift_le_some_iff d d').
Qed.

(* Concrete instance: Some (fin 2) ⊑ Some (fin 5). *)
Lemma test_lift_le_some_concrete :
    (Some (fin 2) : option nat_inf) ⊑ Some (fin 5).
Proof.
  apply (proj2 (lift_le_some_iff (fin 2) (fin 5))).
  rewrite nat_inf_leE. simpl. auto with arith.
Qed.

(* Concrete instance: ¬ Some (fin 5) ⊑ Some (fin 2). *)
Lemma test_lift_le_some_concrete_neg :
    ~ (Some (fin 5) : option nat_inf) ⊑ Some (fin 2).
Proof.
  intro H. apply (proj1 (lift_le_some_iff (fin 5) (fin 2))) in H.
  rewrite nat_inf_leE in H. simpl in H. lia.
Qed.

End LiftLeTests.


(* ================================================================== *)
(* §2  lift_sup — supremum computation                                 *)
(* ================================================================== *)

Section LiftSupTests.

(* A chain of all-None values has supremum None. *)

Definition all_none_chain : chain (option nat_inf) :=
  Build_chain (fun _ => None) (fun _ _ _ => I).

Lemma test_lift_sup_all_none : ⊔ all_none_chain = None.
Proof.
  apply lift_sup_none.
  intro n; reflexivity.
Qed.

(*
    A chain that is None for n < 2 and Some (fin 7) for n >= 2
    has supremum Some (fin 7).
*)

Lemma stabilising_chain_mono :
    forall m n : nat, m <= n ->
    (fun k => if Nat.leb 2 k then Some (fin 7) else (None : option nat_inf)) m ⊑
    (fun k => if Nat.leb 2 k then Some (fin 7) else (None : option nat_inf)) n.
Proof.
  intros m n Hmn.
  destruct (Nat.leb 2 m) eqn:Hm, (Nat.leb 2 n) eqn:Hn.
  - rewrite Hm. exact (le_refl _).
  - rewrite Hm. apply Nat.leb_le in Hm.
    pose proof (Nat.le_trans _ _ _ Hm Hmn) as Htrans.
    apply Nat.leb_le in Htrans.
    pose proof (Bool.diff_true_false).
    rewrite <- Htrans, <- Hn in H.
    exfalso. apply H; reflexivity.
  - rewrite Hm. exact I.
  - rewrite Hm. exact I.
Qed.

Definition stabilising_chain : chain (option nat_inf) :=
  Build_chain
    (fun k => if Nat.leb 2 k then Some (fin 7) else None)
    stabilising_chain_mono.

Lemma test_lift_sup_stabilising :
    ⊔ stabilising_chain = Some (fin 7).
Proof.
  assert (HN : stabilising_chain.[2] <> None).
  { simpl. discriminate. }
  pose proof (lift_sup_some_eq stabilising_chain 2 (fin 7) HN) as Hsup.
  rewrite Hsup.
  f_equal.
  apply nat_inf_sup_const.
  intros n. simpl. unfold D_chain_fn. simpl.
  replace (Nat.leb 2 (2 + n)) with true.
  2: { symmetry. apply Nat.leb_le. lia. }
  reflexivity.
Qed.

(*
    A chain that is always Some (fin 4) has supremum Some (fin 4).
*)

Lemma const_some_chain_mono :
    forall m n : nat, m <= n ->
    (Some (fin 4) : option nat_inf) ⊑ Some (fin 4).
Proof.
  intros. simpl. apply nat_inf_le_refl.
Qed.

Definition const_some_chain : chain (option nat_inf) :=
  Build_chain (fun _ => Some (fin 4)) const_some_chain_mono.

Lemma test_lift_sup_const_some :
    ⊔ const_some_chain = Some (fin 4).
Proof.
  assert (HN : const_some_chain.[0] <> None).
  { simpl. discriminate. }
  pose proof (lift_sup_some_eq const_some_chain 0 (fin 4) HN) as Hsup.
  rewrite Hsup.
  f_equal.
  apply nat_inf_sup_const.
  intro n. simpl. unfold D_chain_fn. simpl.
  reflexivity.
Qed.

End LiftSupTests.


(* ================================================================== *)
(* §3  ret — correctness and continuity                                *)
(* ================================================================== *)

Section RetTests.

(* ret maps d to Some d. *)
Lemma test_ret_some (d : nat_inf) : ret d = Some d.
Proof.
  exact (ret_some d).
Qed.

(* ret is continuous: ret (⊔ c) = ⊔ (map_chain ret c). *)
Lemma test_ret_continuous : continuous (cf_mono (ret (D := nat_inf))).
Proof.
  exact (cf_cont (ret (D := nat_inf))).
Qed.

(*
    Concrete continuity check: apply ret to a constant chain and verify
    the result agrees with the supremum of the mapped chain.
*)

Definition nat_inf_const_chain (v : nat_inf) : chain nat_inf :=
  const_chain v.

Lemma test_ret_continuous_concrete :
    ret (⊔ nat_inf_const_chain (fin 5)) =
    ⊔ (map_chain (cf_mono (ret (D := nat_inf))) (nat_inf_const_chain (fin 5))).
Proof.
  exact (cf_cont ret (nat_inf_const_chain (fin 5))).
Qed.

End RetTests.


(* ================================================================== *)
(* §4  kleisli — computation rules and continuity                      *)
(* ================================================================== *)

Section KleisliTests.

(*
    A test function f : nat_inf →c (option nat_inf) that wraps its
    argument in Some (i.e., f = ret).
*)
Definition test_f : cont_fun nat_inf (option nat_inf) := ret.

(* kleisli f None = None. *)
Lemma test_kleisli_none : kleisli test_f None = None.
Proof.
  exact (kleisli_none test_f).
Qed.

(* kleisli f (Some d) = f d. *)
Lemma test_kleisli_some (d : nat_inf) :
    kleisli test_f (Some d) = test_f d.
Proof.
  exact (kleisli_some test_f d).
Qed.

(* Concrete: kleisli ret (Some (fin 3)) = Some (fin 3). *)
Lemma test_kleisli_some_concrete :
    kleisli (ret (D := nat_inf)) (Some (fin 3)) = Some (fin 3).
Proof.
  reflexivity.
Qed.

(* kleisli is continuous. *)
Lemma test_kleisli_continuous :
    continuous (cf_mono (kleisli test_f)).
Proof.
  exact (cf_cont (kleisli test_f)).
Qed.

(*
    Concrete continuity check on the all-None chain:
    kleisli f (⊔ all_none_chain) = ⊔ (map_chain (kleisli f) all_none_chain).
*)
Lemma test_kleisli_continuous_none_chain :
    kleisli test_f (⊔ all_none_chain) =
    ⊔ (map_chain (cf_mono (kleisli test_f)) all_none_chain).
Proof.
  exact (cf_cont (kleisli test_f) all_none_chain).
Qed.

(*
    Concrete continuity check on the stabilising chain:
    kleisli f (⊔ stabilising_chain) = ⊔ (map_chain (kleisli f) stabilising_chain).
*)
Lemma test_kleisli_continuous_stabilising :
    kleisli test_f (⊔ stabilising_chain) =
    ⊔ (map_chain (cf_mono (kleisli test_f)) stabilising_chain).
Proof.
  exact (cf_cont (kleisli test_f) stabilising_chain).
Qed.

End KleisliTests.


(* ================================================================== *)
(* §5  Monad law — left unit (kleisli f ∘ ret = f)                     *)
(* ================================================================== *)

Section MonadLawTests.

(* The left unit law: kleisli f ∘ ret = f. *)
Lemma test_left_unit :
    cont_comp (kleisli (ret (D := nat_inf))) (ret (D := nat_inf)) =
    ret (D := nat_inf).
Proof.
  exact (kleisli_ret_left ret).
Qed.

(* Pointwise check of the left unit law with an arbitrary function. *)
Definition test_g : cont_fun nat_inf (option nat_inf) := ret.

Lemma test_left_unit_pointwise (d : nat_inf) :
    kleisli test_g (ret d) = test_g d.
Proof.
  reflexivity.
Qed.

(* The general left unit law for any f. *)
Lemma test_left_unit_general (f : cont_fun nat_inf (option nat_inf)) :
    cont_comp (kleisli f) (ret (D := nat_inf)) = f.
Proof.
  exact (kleisli_ret_left f).
Qed.

End MonadLawTests.
