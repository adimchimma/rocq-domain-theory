(*  FunctionSpaceTests

    Unit tests for the function-space CPO [[D →c E]] construction from
    [src/theory/FunctionSpaces.v] and composition operators from
    [src/instances/Function.v].

    Tests:
    - §1  fun_le — pointwise ordering of continuous functions
    - §2  cont_eval — evaluation map
    - §3  curry / uncurry — exponential adjunction
    - §4  Fun pointed — bottom of function space
    - §5  Composition operators — precomp, postcomp, const, apply-at
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory CPOTheory Products
                                        FunctionSpaces FixedPoints.
From DomainTheory.Instances Require Import Nat Function.

From Stdlib Require Import Lia.


(* ================================================================== *)
(* §1  fun_le — pointwise ordering of continuous functions             *)
(* ================================================================== *)

Section FunLeTests.

Definition c3 : [nat_inf →c nat_inf] := cont_const (fin 3).
Definition c5 : [nat_inf →c nat_inf] := cont_const (fin 5).

(* const 3 ⊑ const 5 pointwise. *)
Lemma test_fun_le_const :
    (c3 : [nat_inf →c nat_inf]) ⊑ c5.
Proof.
  unfold fun_le. intro x. simpl.
  apply (proj2 (fin_le 3 5)). lia.
Qed.

(* ¬ const 5 ⊑ const 3. *)
Lemma test_fun_le_neg :
    ~ (c5 : [nat_inf →c nat_inf]) ⊑ c3.
Proof.
  intro H. unfold fun_le in H.
  specialize (H (fin 0)). simpl in H.
  apply (proj1 (fin_le 5 3)) in H. lia.
Qed.

(* id ⊑ id (reflexivity). *)
Lemma test_fun_le_refl :
    (cont_id nat_inf : [nat_inf →c nat_inf]) ⊑ cont_id nat_inf.
Proof. intro x. apply le_refl. Qed.

End FunLeTests.


(* ================================================================== *)
(* §2  cont_eval — evaluation map                                     *)
(* ================================================================== *)

Section EvalTests.

(* cont_eval (f, x) = f x. *)
Lemma test_cont_eval_apply :
    cont_eval (cont_const (fin 7) : [nat_inf →c nat_inf], fin 2) = fin 7.
Proof. reflexivity. Qed.

(* cont_eval agrees with the direct application lemma. *)
Lemma test_cont_eval_lemma (f : [nat_inf →c nat_inf]) (x : nat_inf) :
    cont_eval (f, x) = f x.
Proof. exact (cont_eval_apply f x). Qed.

(* cont_eval is continuous. *)
Lemma test_cont_eval_continuous :
    continuous (cf_mono (cont_eval (D := nat_inf) (E := nat_inf))).
Proof. exact (cf_cont cont_eval). Qed.

End EvalTests.


(* ================================================================== *)
(* §3  curry / uncurry — exponential adjunction                        *)
(* ================================================================== *)

Open Scope type_scope.
Section CurryUncurryTests.

(* 
    Test function: cont_eval : (D →c E) * D →c E.
    curry cont_eval : (D →c E) →c (D →c E) should be the identity.
*)

(* curry computation. *)
Lemma test_curry_apply :
    forall (f : [nat_inf →c nat_inf]) (x : nat_inf),
    cont_curry (cont_eval (D := nat_inf) (E := nat_inf)) f x = f x.
Proof.
  intros f x.
  exact (cont_curry_apply cont_eval f x).
Qed.

(* uncurry computation. *)
Lemma test_uncurry_apply :
    forall (f : [nat_inf →c nat_inf]) (x : nat_inf),
    cont_uncurry (cont_id [nat_inf →c nat_inf]) (f, x) =
    (cont_id [nat_inf →c nat_inf]) f x.
Proof.
  intros f x.
  exact (cont_uncurry_apply (cont_id [nat_inf →c nat_inf]) f x).
Qed.

(* Round-trip: curry (uncurry f) = f. *)
Lemma test_curry_uncurry (f : [nat_inf →c [nat_inf →c nat_inf]]) :
    cont_curry (cont_uncurry f) = f.
Proof. exact (curry_uncurry f). Qed.

(* Round-trip: uncurry (curry f) = f. *)
Lemma test_uncurry_curry (f : [nat_inf * nat_inf →c nat_inf]) :
    cont_uncurry (cont_curry f) = f.
Proof. exact (uncurry_curry f). Qed.

(* eval ∘ (curry f × id) = f. *)
Lemma test_eval_curry (f : [nat_inf * nat_inf →c nat_inf]) :
    cont_comp cont_eval (cont_prod_map (cont_curry f) (cont_id nat_inf)) = f.
Proof. exact (eval_curry f). Qed.

End CurryUncurryTests.
Close Scope type_scope.

(* ================================================================== *)
(* §4  Fun pointed — bottom of function space                          *)
(* ================================================================== *)

Section FunPointedTests.

(* The bottom of (nat_inf →c nat_inf) maps everything to ⊥. *)
Lemma test_fun_bottom :
    (⊥ : [nat_inf →c nat_inf]) (fin 5) = (⊥ : nat_inf).
Proof. reflexivity. Qed.

(* ⊥ ⊑ every function. *)
Lemma test_fun_bottom_least (f : [nat_inf →c nat_inf]) :
    (⊥ : [nat_inf →c nat_inf]) ⊑ f.
Proof. apply @bottom_least. Qed.

End FunPointedTests.


(* ================================================================== *)
(* §5  Composition operators — const, apply-at, flip                   *)
(* ================================================================== *)

Section CompOpTests.

(* cont_const computation. *)
Lemma test_cont_const_apply :
    cont_const (fin 7) (fin 2 : nat_inf) = (fin 7 : nat_inf).
Proof. exact (cont_const_apply (fin 7) (fin 2)). Qed.

(* cont_K computation: K e d = e. *)
Lemma test_cont_K :
    (cont_K (D := nat_inf) (E := nat_inf)) (fin 7) (fin 2) = fin 7.
Proof. exact (cont_K_apply (fin 7) (fin 2)). Qed.

(* cont_ap computation: cont_ap x f = f x. *)
Lemma test_cont_ap :
    cont_ap (fin 3) (cont_const (fin 7) : [nat_inf →c nat_inf]) = fin 7.
Proof. exact (cont_ap_apply (fin 3) (cont_const (fin 7))). Qed.

(* cont_postcomp computation. *)
Lemma test_cont_postcomp :
    cont_postcomp (cont_const (fin 9) : [nat_inf →c nat_inf])
                  (cont_id nat_inf) (fin 5) = fin 9.
Proof.
  exact (cont_postcomp_apply (cont_const (fin 9)) (cont_id nat_inf) (fin 5)).
Qed.

(* cont_precomp computation. *)
Lemma test_cont_precomp :
    cont_precomp (cont_const (fin 2) : [nat_inf →c nat_inf])
                 (cont_id nat_inf) (fin 5) = fin 2.
Proof.
  exact (cont_precomp_apply (cont_const (fin 2)) (cont_id nat_inf) (fin 5)).
Qed.

(* cont_flip involutive. *)
Lemma test_cont_flip_involutive (f : [nat_inf →c [nat_inf →c nat_inf]]) :
    cont_flip (cont_flip f) = f.
Proof. exact (cont_flip_involutive f). Qed.

End CompOpTests.

