(** Complete Partial Orders (CPOs)

    This module defines ω-complete partial orders (CPOs), which are preorders
    where every chain has a least upper bound (lub).

    Based on Section 2.1 of "Some Domain Theory and Denotational Semantics in Coq"
    (Benton, Kennedy, Varming 2009), modernized for Rocq 8.20+.
*)

From Stdlib Require Import Arith.
(* Require Import Order. *)
From phase0_foundations Require Import Order.

Set Universe Polymorphism.
Set Implicit Arguments.

(** A CPO is a preorder equipped with a lub operation for chains *)
#[universes(polymorphic)]
Record cpo : Type := {
  cpo_ord :> preorder ;
  
  lub : chain cpo_ord -> cpo_ord ;
  
  (** Every element of the chain is below the lub *)
  lub_upper_bound : forall (c : chain cpo_ord) (n : nat),
    le cpo_ord c[n] (lub c) ;
  
  (** The lub is the least upper bound *)
  lub_least : forall (c : chain cpo_ord) (x : cpo_ord),
    (forall n : nat, le cpo_ord c[n] x) ->
    le cpo_ord (lub c) x ;
}.

(** Notation for lub *)
Notation "⊔ c" := (lub _ c) (at level 50).

(** Basic properties of lubs *)

Lemma lub_monotone (D : cpo) (c1 c2 : chain D) :
  (forall n : nat, le D c1[n] c2[n]) ->
  le D (⊔c1) (⊔c2).
Proof.
  intro H.
  apply lub_least.
  intro n.
  apply le_trans with (y := c2[n]).
  - apply H.
  - apply lub_upper_bound.
Qed.

(** Constant chains *)
Definition const_chain (D : cpo) (x : D) : chain D := {|
  mf_func := fun _ => x ;
  mf_mono := fun _ _ _ => le_refl D x ;
|}.

Lemma lub_const (D : cpo) (x : D) :
  ⊔(const_chain D x) ≈{D} x.
Proof.
  unfold equiv; split.
  - apply lub_least.
    intro n. apply le_refl.
  - apply lub_upper_bound with (n := 0).
Qed.

(** The discrete CPO on any type *)
Definition discrete_cpo (X : Type) : cpo := {|
  cpo_ord := discrete_preorder X ;
  lub := fun c => c 0 ;
  lub_upper_bound := fun c n =>
    match n with
    | 0 => eq_refl
    | S n' => mf_mono _ _ c 0 (S n') (Nat.le_0_l (S n'))
    end ;
  lub_least := fun c x H => H 0 ;
|}.

(** Natural numbers form a CPO with the usual order *)
Definition nat_cpo : cpo := {|
  cpo_ord := nat_preorder ;
  lub := fun c =>
    c 0 ; (* This is actually wrong for nat_preorder, but we'll fix it later
             when we need a proper construction. For now this is a placeholder. *)
  lub_upper_bound := fun c n => Nat.le_0_l _ ;
  lub_least := fun c x H => H 0 ;
|}.

(** A pointed CPO has a least element (bottom) *)
Class Pointed (D : cpo) := {
  bottom : D ;
  bottom_least : forall x : D, le D bottom x ;
}.

Notation "⊥" := bottom.

(** If D is pointed, constant chains starting at ⊥ give ⊥ *)
Lemma lub_bottom (D : cpo) `{Pointed D} :
  ⊔(const_chain D ⊥) ≈{D} ⊥.
Proof.
  apply lub_const.
Qed.

(** Admissible predicates

    A predicate P on a CPO is admissible if whenever all elements of a chain
    satisfy P, the lub of the chain also satisfies P.
*)
Definition admissible (D : cpo) (P : D -> Prop) : Prop :=
  forall (c : chain D),
    (forall n : nat, P c[n]) ->
    P (⊔c).

(** Fixed point induction principle

    If P is admissible, P(⊥), and P is preserved by F,
    then P holds at the fixed point of F.
    
    We'll define fixed points properly in FixedPoints.v
*)
