(** Unit tests for CPO basics

    Tests:
    - lub_upper and lub_least properties
    - discrete cpo instance
    - unit cpo instance
*)

From phase0_foundations Require Import CPO Order Discrete.

Module Tests_CPO.

(** Test 1: Unit CPO satisfies lub properties *)
Example unit_cpo_lub : forall (c : nat -> Discrete.unit_cpo),
    Cpo.lub_upper Discrete.unit_cpo c 0.
Proof.
  intros c.
  exact I.
Qed.

(** Test 2: Unit CPO lub is least upper bound *)
Example unit_cpo_lub_least : forall (c : nat -> Discrete.unit_cpo) (x : Discrete.unit_cpo) 
    (H : forall n, le (Cpo.cpo_pre Discrete.unit_cpo) (c n) x),
    le (Cpo.cpo_pre Discrete.unit_cpo) (Cpo.lub_of_chain Discrete.unit_cpo c) x.
Proof.
  intros c x H.
  exact I.
Qed.

(** Test 3: Preorder coercion works *)
Example cpo_coercion (D : Cpo.cpo) : Order.preorder :=
  Cpo.cpo_to_pre D.

(** Test 4: Carrier coercion works *)
Example carrier_coercion (D : Cpo.cpo) (x : D) : carrier (Cpo.cpo_pre D) :=
  (x : carrier (Cpo.cpo_pre D)).

End Tests_CPO.
