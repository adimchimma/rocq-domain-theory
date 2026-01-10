(* Cpo.v *)
Require Import Arith.
From phase0_foundations Require Import Order.
Import Order.

Module Cpo.

Set Universe Polymorphism.
Monomorphic Universe u.

(** A CPO: an underlying preorder plus a computable lub for chains nat -> D. *)
Record cpo := {
  cpo_pre :> preorder ;
  lub_of_chain : (nat -> carrier cpo_pre) -> carrier cpo_pre ;
  lub_upper : forall (c : nat -> carrier cpo_pre) n, le cpo_pre (c n) (lub_of_chain c) ;
  lub_least : forall (c : nat -> carrier cpo_pre) x, (forall n, le cpo_pre (c n) x) -> le cpo_pre (lub_of_chain c) x
}.

Coercion cpo_to_pre (D : cpo) : preorder := cpo_pre D.

(** Monotone functions between cpos (reuse mono_fun on preorders) *)
Definition mono (D E : cpo) := mono_fun D E.

(** Continuous functions: preserve lubs of chains (up to preorder). *)
(* Helper to apply lub_of_chain to chains over cpo objects (coercions handle carriers) *)
Definition lub_of_chain_D (D : cpo) (c : nat -> D) : D := lub_of_chain (fun n => (c n : carrier (cpo_pre D))).

Definition continuous (D E : cpo) (f : D -> E) : Prop :=
  forall (c : nat -> D), le (cpo_pre E) (f (lub_of_chain_D D c)) (lub_of_chain_D E (fun n => f (c n))).

Record cont_fun (D E : cpo) := {
  cf_func :> D -> E ;
  cf_cont : continuous D E cf_func
}.

Coercion cf_func : cont_fun >-> Funclass.

(** Pointwise function space: D => E as a cpo *)
Definition fun_cpo (D E : cpo) : cpo.
Proof.
  refine ({| cpo_pre := {|
       carrier := (cont_fun D E);
       le := fun f g => forall x, le (f x) (g x);
       le_refl := _;
       le_trans := _
     |};
     lub_of_chain := fun (c : nat -> cont_fun D E) =>
       (* pointwise lub: build function mapping x to lub (fun n => c n x) *)
       {| cf_func := fun x => lub_of_chain (fun n => (c n) x);
          cf_cont := _
       |};
     lub_upper := _;
     lub_least := _
  |}).
  - intros f x; apply le_refl.
  - intros f g h Hfg Hgh x; apply (le_trans _ _ _ (Hfg x) (Hgh x)).
  - (* continuity of constructed function *)
    intros D0 E0 d.
    simpl.
    apply lub_least.
    intros k.
    specialize (cf_cont (c k) d) as Hck.
    apply (le_trans _ _ _ Hck).
    apply lub_least. intros m.
    apply le_trans with (lub_of_chain (fun t => (c t) (d m))).
    + apply lub_upper.
    + apply lub_least. intros t. apply lub_upper.
  - intros c n x; simpl; apply lub_upper.
  - intros c x H y;
      simpl; apply (lub_least (fun n => (c n) y) (x y)); intros n; apply (H n y).
Defined.


(* prod_cpo moved to `Products.v` *)
(* See `Products.v` for product CPO implementation. *)

(** Pointed cpos and least fixed point operator *)
Class Pointed (D : cpo) := { bottom : D ; bottom_least : forall d : D, le bottom d }.

Section Fixpoint.
  Context {D : cpo} {PD : Pointed D}.

  (** iterate F starting from bottom *)
  Fixpoint iter (F : D -> D) (n : nat) : D :=
    match n with
    | 0 => bottom
    | S k => F (iter F k)
    end.

  Definition fixp (F : D -> D) : D := lub_of_chain (fun n => iter F n).

  (** Fixed point induction principle (statement) *)
  Theorem fixp_ind (F : D -> D) (P : D -> Prop) :
    (forall c, (forall n, P (c n)) -> P (lub_of_chain c)) ->
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

End Fixpoint.

End Cpo.
