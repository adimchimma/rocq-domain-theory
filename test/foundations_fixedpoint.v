(** Unit tests for Fixed Points

    Tests:
    - Fixed point iteration
    - Least fixed point properties
    - Fixed point induction principle
*)

From phase0_foundations Require Import CPO Order Discrete Pointed.

Module Tests_FixedPoints.

Let D := Discrete.unit_cpo.

(** Test 1: Unit CPO is pointed *)
Instance unit_cpo_pointed : Cpo.Pointed D := {|
  Cpo.bottom := tt ;
  Cpo.bottom_least := fun _ => I
|}.

(** Test 2: Fixed point iteration starting from bottom *)
Example fixp_iter_zero (F : D -> D) :
    Cpo.iter F 0 = Cpo.bottom.
Proof.
  reflexivity.
Qed.

(** Test 3: Fixed point operator defined *)
Example fixp_defined (F : D -> D) : D :=
  Cpo.fixp F.

(** Test 4: Fixed point induction principle applies *)
Example fixp_ind_applies (F : D -> D) (P : D -> Prop) :
    (forall c, (forall n, P (c n)) -> P (Cpo.lub_of_chain D c)) ->
    P Cpo.bottom ->
    (forall x, P x -> P (F x)) ->
    P (Cpo.fixp F).
Proof.
  exact Cpo.fixp_ind F P.
Qed.

End Tests_FixedPoints.
