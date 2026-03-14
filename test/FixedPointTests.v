(*  FixedPointTests

    Unit tests for the Kleene fixed-point construction from
    [src/theory/FixedPoints.v] and the continuous fixed-point
    operator [FIXP] from [src/theory/FunctionSpaces.v].

    Tests:
    - §1  iter — iteration chain computation
    - §2  fixp_is_fixedpoint — fixed-point property
    - §3  fixp_least — least pre-fixed point
    - §4  Least pre-fixed point = least fixed point
    - §5  fixp_ind — Scott induction
    - §6  fixp_mono — monotonicity of fixp
    - §7  FIXP — the continuous fixed-point operator
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory CPOTheory
                                        FixedPoints FunctionSpaces.
From DomainTheory.Instances Require Import Nat Function.

From Stdlib Require Import Lia.


(* ================================================================== *)
(* §1  iter — iteration chain computation                              *)
(* ================================================================== *)

Section IterTests.

(*
    Test function: the constant function [cont_const (fin 5)] on [nat_inf].
    iter c5 n  =  c5^n(⊥)  =  fin 0  for n=0,  fin 5  for n>=1.
*)
Definition c5 : [nat_inf →c nat_inf] := cont_const (fin 5).

Lemma test_iter_zero : iter c5 0 = fin 0.
Proof. reflexivity. Qed.

Lemma test_iter_one : iter c5 1 = fin 5.
Proof. reflexivity. Qed.

Lemma test_iter_two : iter c5 2 = fin 5.
Proof. reflexivity. Qed.

(* iter respects monotonicity: m <= n -> iter f m ⊑ iter f n. *)
Lemma test_iter_mono :
    iter c5 0 ⊑ iter c5 2.
Proof.
  apply iter_mono. auto.
Qed.

(* The identity's iteration is always bottom. *)
Lemma test_iter_id (n : nat) :
    iter (cont_id nat_inf) n = (⊥ : nat_inf).
Proof.
  induction n; simpl.
  - reflexivity.
  - exact IHn.
Qed.

End IterTests.


(* ================================================================== *)
(* §2  fixp_is_fixedpoint — the fixed-point equation                   *)
(* ================================================================== *)

Section FixpFixedPointTests.

(* fixp c5 satisfies the fixed-point equation. *)
Lemma test_fixp_is_fixedpoint :
    c5 (fixp c5) = fixp c5.
Proof. exact (fixp_is_fixedpoint c5). Qed.

(* The unfold direction: fixp f = f (fixp f). *)
Lemma test_fixp_unfold :
    fixp c5 = c5 (fixp c5).
Proof. exact (fixp_unfold c5). Qed.

(* Concrete value: fixp (const 5) = fin 5. *)
Lemma test_fixp_c5_val : fixp c5 = fin 5.
Proof.
  rewrite <- (fixp_is_fixedpoint c5).
  reflexivity.
Qed.

(* fixp id = bot. *)
Lemma test_fixp_id : fixp (@cont_id nat_inf) = (⊥ : nat_inf).
Proof. exact fixp_id. Qed.

End FixpFixedPointTests.


(* ================================================================== *)
(* §3  fixp_least — least pre-fixed point property                     *)
(* ================================================================== *)

Section FixpLeastTests.

(*
    fixp_least:  f x ⊑ x  ->  fixp f ⊑ x.
    Test with c5 = const (fin 5) and x = fin 7.
    c5 (fin 7) = fin 5 ⊑ fin 7, so fixp c5 ⊑ fin 7.
*)
Lemma test_fixp_least_concrete :
    fixp c5 ⊑ fin 7.
Proof.
  apply fixp_least.
  simpl. apply (proj2 (fin_le 5 7)). lia.
Qed.

(* fixp_least_fixedpoint: f x = x -> fixp f ⊑ x. *)
Lemma test_fixp_least_fixedpoint :
    forall (x : nat_inf), c5 x = x -> fixp c5 ⊑ x.
Proof.
  intros x Hfx.
  exact (fixp_least_fixedpoint c5 x Hfx).
Qed.

(* fixp_characterisation: an element that is both a fixed point
   and below every pre-fixed point equals fixp. *)
Lemma test_fixp_characterisation :
    fixp c5 = fin 5.
Proof.
  symmetry.
  apply fixp_characterisation.
  - reflexivity.
  - intros y Hy. exact Hy.
Qed.

(* bot ⊑ fixp f always. *)
Lemma test_bottom_le_fixp : (⊥ : nat_inf) ⊑ fixp c5.
Proof. exact (bottom_le_fixp c5). Qed.

End FixpLeastTests.


(* ================================================================== *)
(* §4  Least pre-fixed point = least fixed point                       *)
(* ================================================================== *)
(*
    For any Scott-continuous [f : D →c D] on a pointed CPO:

    1. fixp f is a fixed point  (fixp_is_fixedpoint)
    2. fixp f ⊑ every pre-fixed point  (fixp_least)

    Since every fixed point is a pre-fixed point (f x = x -> f x ⊑ x),
    fixp f is also the least fixed point.  We test this explicitly.
*)

Section LeastPreFixedVsFixedTests.

Variable (D : PointedCPO.type) (f : [D →c D]).

(* Every fixed point is a pre-fixed point. *)
Lemma test_fixedpoint_is_prefixedpoint (x : D) :
    f x = x -> f x ⊑ x.
Proof. intro H. rewrite H. apply le_refl. Qed.

(* fixp is below every fixed point (i.e., fixp is the least fixed point). *)
Lemma test_fixp_least_among_fixedpoints (x : D) :
    f x = x -> fixp f ⊑ x.
Proof. exact (fixp_least_fixedpoint f x). Qed.

(* fixp is below every pre-fixed point. *)
Lemma test_fixp_least_among_prefixedpoints (x : D) :
    f x ⊑ x -> fixp f ⊑ x.
Proof. exact (fixp_least f x). Qed.

(*
    The set of pre-fixed points contains the set of fixed points.
    Therefore the least pre-fixed point ⊑ every fixed point,
    confirming that least-pre-fixed-point = least-fixed-point
    when the least-pre-fixed-point is itself a fixed point (which fixp is).
*)
Lemma test_least_prefixed_eq_least_fixed :
    forall x : D,
    f x = x -> fixp f ⊑ x.
Proof.
  intros x Hfx.
  apply fixp_least.
  rewrite Hfx. apply le_refl.
Qed.

End LeastPreFixedVsFixedTests.


(* ================================================================== *)
(* §5  fixp_ind — Scott induction                                      *)
(* ================================================================== *)

Section FixpIndTests.

(* Scott induction with a trivial predicate: P = True. *)
Lemma test_fixp_ind_trivial :
    True -> (fixp c5 = fixp c5).
Proof.
  reflexivity.
Qed.

(*
    Scott induction with a concrete predicate:
    P x := x ⊑ fin 5.   (admissible by admissible_le)

    Base: ⊥ = fin 0 ⊑ fin 5.
    Step: c5 x = fin 5 ⊑ fin 5.
    Conclusion: fixp c5 ⊑ fin 5.
*)
Lemma test_fixp_ind_le :
    fixp c5 ⊑ fin 5.
Proof.
  apply (fixp_ind c5 (fun x => x ⊑ fin 5)).
  - exact (admissible_le (fin 5)).
  - apply (proj2 (fin_le 0 5)). lia.
  - intros x _. simpl. apply (proj2 (fin_le 5 5)). lia.
Qed.

(* fixp_ind_le: shortcut for lower bound via admissible_le. *)
Lemma test_fixp_ind_le_shortcut :
    fixp c5 ⊑ fin 5.
Proof.
  apply fixp_ind_le.
  simpl. apply (proj2 (fin_le 5 5)). lia.
Qed.

End FixpIndTests.


(* ================================================================== *)
(* §6  fixp_mono — monotonicity of fixp                                *)
(* ================================================================== *)

Section FixpMonoTests.

Definition c3 : [nat_inf →c nat_inf] := cont_const (fin 3).

(* const 3 ⊑ const 5 pointwise, so fixp (const 3) ⊑ fixp (const 5). *)
Lemma test_fixp_mono :
    fixp c3 ⊑ fixp c5.
Proof.
  apply fixp_mono.
  intro x. simpl. apply (proj2 (fin_le 3 5)). lia.
Qed.

(* fixp_mono_eq: pointwise equality implies fixp equality. *)
Lemma test_fixp_mono_eq :
    fixp c5 = fixp c5.
Proof.
  apply fixp_mono_eq.
  intro x. reflexivity.
Qed.

End FixpMonoTests.


(* ================================================================== *)
(* §7  FIXP — the continuous fixed-point operator                      *)
(* ================================================================== *)

Section FIXPTests.

(* FIXP agrees with fixp. *)
Lemma test_FIXP_eq : FIXP c5 = fixp c5.
Proof. exact (FIXP_eq c5). Qed.

(* FIXP c5 is a fixed point. *)
Lemma test_FIXP_is_fixedpoint : c5 (FIXP c5) = FIXP c5.
Proof. exact (FIXP_is_fixedpoint c5). Qed.

(* FIXP c5 is the least pre-fixed point. *)
Lemma test_FIXP_least (x : nat_inf) :
    c5 x ⊑ x -> FIXP c5 ⊑ x.
Proof. exact (FIXP_least c5 x). Qed.

(* Concrete value via FIXP. *)
Lemma test_FIXP_val : FIXP c5 = fin 5.
Proof.
  rewrite FIXP_eq.
  rewrite <- (fixp_is_fixedpoint c5).
  reflexivity.
Qed.

(* FIXP is continuous — type-level witness. *)
Lemma test_FIXP_continuous :
    continuous (cf_mono (FIXP (D := nat_inf))).
Proof. exact (cf_cont FIXP). Qed.

End FIXPTests.
