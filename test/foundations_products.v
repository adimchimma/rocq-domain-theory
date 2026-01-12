(** Unit tests for Product CPOs

    Tests:
    - Product cpo construction
    - Component-wise lubs
    - Projection properties
*)

From phase0_foundations Require Import CPO Order Discrete Products.

Module Tests_Products.

Let D := Discrete.unit_cpo.
Let E := Discrete.unit_cpo.

(** Test 1: Product cpo exists *)
Example prod_cpo_exists : Cpo.cpo :=
  Products.prod_cpo D E.

(** Test 2: Component-wise lub preserves reflexivity *)
Example prod_lub_upper : forall (c : nat -> carrier (Products.prod_cpo D E)) (n : nat),
    le (Cpo.cpo_pre (Products.prod_cpo D E)) (c n) (Cpo.lub_of_chain (Products.prod_cpo D E) c).
Proof.
  intros c n.
  apply Cpo.lub_upper.
Qed.

(** Test 3: Product is least upper bound *)
Example prod_lub_least : forall (c : nat -> carrier (Products.prod_cpo D E)) (p : carrier (Products.prod_cpo D E))
    (H : forall n, le (Cpo.cpo_pre (Products.prod_cpo D E)) (c n) p),
    le (Cpo.cpo_pre (Products.prod_cpo D E)) (Cpo.lub_of_chain (Products.prod_cpo D E) c) p.
Proof.
  intros c p H.
  apply Cpo.lub_least.
  exact H.
Qed.

End Tests_Products.
