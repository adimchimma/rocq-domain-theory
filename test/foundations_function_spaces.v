(** Unit tests for Function Space CPOs

    Tests:
    - Function space cpo construction
    - Pointwise order preservation
    - Continuity of identity
*)

From phase0_foundations Require Import CPO Order Continuous FunctionSpaces Discrete.

Module Tests_FunctionSpaces.

Let D := Discrete.unit_cpo.
Let E := Discrete.unit_cpo.

(** Test 1: Function space CPO exists *)
Example fun_cpo_exists : Cpo.cpo :=
  FunctionSpaces.fun_cpo D E.

(** Test 2: Identity is continuous *)
Example id_continuous : Continuous.continuous D D (fun x => x).
Proof.
  exact Continuous.id_continuous D.
Qed.

(** Test 3: Function space lub is upper bound *)
Example fun_lub_upper : forall (c : nat -> Continuous.cont_fun D E) (n : nat),
    le (Cpo.cpo_pre (FunctionSpaces.fun_cpo D E)) (c n) (Cpo.lub_of_chain (FunctionSpaces.fun_cpo D E) c).
Proof.
  intros c n.
  apply Cpo.lub_upper.
Qed.

End Tests_FunctionSpaces.
