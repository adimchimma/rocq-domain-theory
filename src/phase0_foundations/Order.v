(** Preorders and Partial Orders

    This module formalizes the basic theory of preorders and partial orders,
    which serve as the foundation for complete partial orders (CPOs).

    Based on Section 2.1 of "Some Domain Theory and Denotational Semantics in Coq"
    (Benton, Kennedy, Varming 2009), modernized for Rocq 8.20+.
*)

Require Import Arith.
Require Import Setoid Morphisms RelationClasses.

(* Require Import Arith.
Require Import Setoid.
Require Import Morphisms.
Require Import RelationClasses. *)


Module Order.

Set Universe Polymorphism.
Monomorphic Universe u.

(** A preorder consists of a type with a reflexive, transitive relation. *)
Record preorder : Type := {
  carrier : Type ;
  le : carrier -> carrier -> Prop ;
  le_refl : forall x : carrier, le x x ;
  le_trans : forall x y z : carrier, le x y -> le y z -> le x z ;
}.

(** Coercion allows us to use a preorder as its carrier type. *)
Coercion carrier : preorder >-> Sortclass.

(** Infix notation for the order relation. *)
Infix "⊑" := (fun ord => @le ord) (at level 70, no associativity).

(** Equivalence in a preorder: x ≈ y iff x ⊑ y and y ⊑ x *)
(* Anti-symmetry *)
Definition equiv (ord : preorder) (x y : ord) : Prop :=
  le ord x y /\ le ord y x.

(* Infix "≈" := equiv (at level 70, no associativity). *)
Notation "lhs ≈{ R } rhs" := (equiv R lhs rhs) (at level 70, no associativity).

(** Basic properties of equivalence *)
Lemma equiv_refl (ord : preorder) : forall x : ord, x ≈{ord} x.
Proof.
  intro x.
  unfold equiv.
  exact (conj (le_refl ord x) (le_refl ord x)).
Qed.

Lemma equiv_sym (ord : preorder) : forall x y : ord, x ≈{ord} y -> y ≈{ord} x.
Proof.
  intros x y (h1, h2).
  exact (conj h2 h1).
Qed.

Lemma equiv_trans (ord : preorder) : forall x y z : ord, x ≈{ord} y -> y ≈{ord} z -> x ≈{ord} z.
Proof.
  intros x y z (h1, h2) (h3, h4).
  exact (conj (le_trans ord x y z h1 h3) (le_trans ord z y x h4 h2)).
Qed.

(** Partial order: a preorder where equivalence implies equality *)
Record partial_order : Type := {
  po_preorder :> preorder ;
  po_antisym : forall x y : po_preorder, x ≈{po_preorder} y -> x = y ;
}.

(** Monotone functions preserve the order relation *)
Definition monotone (ord1 ord2 : preorder) (f : ord1 -> ord2) : Prop :=
  forall x y : ord1, le ord1 x y -> le ord2 (f x) (f y).

(** A type of monotone functions *)
Record mono_fun (ord1 ord2 : preorder) := {
  mf_func :> ord1 -> ord2 ;
  mf_mono : monotone ord1 ord2 mf_func ;
}.

(** The identity monotone function *)
Definition mono_id (ord : preorder) : mono_fun ord ord := {|
  mf_func := fun x => x ;
  mf_mono := fun x y h => h ;
|}.

(** Composition of monotone functions *)
Definition mono_comp (ord1 ord2 ord3 : preorder)
    (g : mono_fun ord2 ord3) (f : mono_fun ord1 ord2) : mono_fun ord1 ord3 := {|
  mf_func := fun x => g (f x) ;
  mf_mono := fun x y h => @mf_mono ord2 ord3 g (f x) (f y) (@mf_mono ord1 ord2 f x y h) ;
|}.

(** Composition is associative *)
Lemma mono_comp_assoc (ord1 ord2 ord3 ord4 : preorder)
    (h : mono_fun ord3 ord4) (g : mono_fun ord2 ord3) (f : mono_fun ord1 ord2) :
  @mono_comp ord1 ord3 ord4 h (@mono_comp ord1 ord2 ord3 g f) =
  @mono_comp ord1 ord2 ord4 (@mono_comp ord2 ord3 ord4 h g) f.
Proof.
  reflexivity.
Qed.

(** Left identity *)
Lemma mono_comp_id_l (ord1 ord2 : preorder) (f : mono_fun ord1 ord2) :
  @mono_comp ord1 ord1 ord2 f (mono_id ord1) = f.
Proof.
  destruct f as [f_func f_mono].
  reflexivity.
Qed.

(** Right identity *)
Lemma mono_comp_id_r (ord1 ord2 : preorder) (f : mono_fun ord1 ord2) :
  @mono_comp ord1 ord2 ord2 (@mono_id ord2) f = f.
Proof.
  destruct f as [f_func f_mono].
  reflexivity.
Qed.

(** The category of preorders and monotone functions *)
(* This is implicit in the definitions above; we could formalize it
   more explicitly using category theory, but for now we work with
   preorders and monotone functions directly. *)

(** Example: The discrete preorder on any type *)
(* Definition discrete_preorder (X : Type@{u}) : preorder := {| *)
Definition discrete_preorder (X : Type) : preorder := {|
  carrier := X ;
  le := fun x y => x = y ;
  le_refl := fun x => eq_refl x ;
  le_trans := fun x y z h1 h2 => eq_trans h1 h2 ;
|}.


(** Example: Natural numbers with the usual order *)
Definition nat_preorder : preorder := {|
  carrier := nat ;
  le := fun x y => x <= y ;
  le_refl := Nat.le_refl ;
  le_trans := Nat.le_trans ;
|}.

(** A chain in a preorder is a monotone function from nat_preorder *)
Definition chain (ord : preorder) : Type :=
  mono_fun nat_preorder ord.

(** Extract the n-th element of a chain *)
Definition chain_at (ord : preorder) (c : chain ord) (n : nat) : ord :=
  c n.

Notation "c [ n ]" := (chain_at _ c n) (at level 9).

End Order.