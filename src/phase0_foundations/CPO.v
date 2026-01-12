(* Cpo.v *)
From phase0_foundations Require Import Order.
Import Order.

Module Cpo.

Set Universe Polymorphism.
Monomorphic Universe u.

(** A CPO: an underlying preorder plus a computable lub for ω-chains. *)
Record cpo := {
  cpo_pre :> preorder ;
  lub_of_chain : chain cpo_pre -> carrier cpo_pre ;
  lub_upper : forall (c : chain cpo_pre) n, le cpo_pre (ch cpo_pre c n) (lub_of_chain c) ;
  lub_least : forall (c : chain cpo_pre) x, (forall n, le cpo_pre (ch cpo_pre c n) x) -> le cpo_pre (lub_of_chain c) x
}.

Coercion cpo_to_pre (D : cpo) : preorder := cpo_pre D.

(** Monotone functions between cpos (reuse mono_fun on preorders) *)
Definition mono (D E : cpo) := mono_fun D E.

(* continuous/cont_fun moved to `Continuous.v` *)
(* See `Continuous.v` for the continuity predicate and the `cont_fun` record. *)

(* fun_cpo moved to `FunctionSpaces.v` *)


(* prod_cpo moved to `Products.v` *)
(* See `Products.v` for product CPO implementation. *)

(** Pointed cpos and least fixed point operator *)
Class Pointed (D : cpo) := { bottom : D ; bottom_least : forall d : D, le (cpo_pre D) bottom d }.

Section Fixpoints.
  Context {D : cpo} {PD : Pointed D}.

  (** iterate F starting from bottom *)
  Fixpoint iter (F : D -> D) (n : nat) : D :=
    match n with
    | 0 => bottom
    | S k => F (iter F k)
    end.

  (** Build chain from iterates **)
  (* TODO: prove monotonicity properly *)
  Axiom iter_mono : forall (F : D -> D) (m n : nat), m <= n -> le (cpo_pre D) (iter F m) (iter F n).
  
  Definition iter_chain (F : D -> D) : chain (cpo_pre D) :=
    Build_chain (cpo_pre D) (fun n => iter F n) (iter_mono F).

  (** least fixed point as lub of iterates (use explicit projections to avoid coercion ambiguity) *)
  Definition fixp (F : D -> D) : D := (Cpo.lub_of_chain D (iter_chain F) : D).

  (** Fixed point induction principle (statement) *)
  Theorem fixp_ind (F : D -> D) (P : D -> Prop) :
    (forall c : chain (cpo_pre D), (forall n, P (ch (cpo_pre D) c n)) -> P (Cpo.lub_of_chain D c)) ->
    P bottom ->
    (forall x, P x -> P (F x)) ->
    P (fixp F).
  Proof.
    intros Hadm Hbot Hstep.
    unfold fixp.
    apply Hadm.
    intros n.
    induction n.
    - exact Hbot.
    - apply Hstep; assumption.
  Qed.

End Fixpoints.

End Cpo.
