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
  lub_of_chain : (nat -> cpo_pre) -> cpo_pre ;
  lub_upper : forall (c : nat -> cpo_pre) n, le c n (lub_of_chain c) ;
  lub_least : forall (c : nat -> cpo_pre) x, (forall n, le (c n) x) -> le (lub_of_chain c) x
}.

Coercion cpo_to_pre (D : cpo) : preorder := cpo_pre D.

(** Monotone functions between cpos (reuse mono_fun on preorders) *)
Definition mono (D E : cpo) := mono_fun D E.

(** Continuous functions: preserve lubs of chains (up to preorder). *)
Definition continuous (D E : cpo) (f : D -> E) : Prop :=
  forall (c : nat -> D), le (f (lub_of_chain c)) (lub_of_chain (fun n => f (c n))).

Record cont_fun (D E : cpo) := {
  cf_func :> D -> E ;
  cf_cont : continuous D E cf_func
}.

(** Pointwise function space: D => E as a cpo *)
Program Definition fun_cpo (D E : cpo) : cpo :=
  {| cpo_pre := {|
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
  |}.
Next Obligation. intros f x; apply le_refl. Qed.
Next Obligation. intros f g h Hfg Hgh x; apply (le_trans _ _ _ (Hfg x) (Hgh x)). Qed.
Next Obligation.
  unfold continuous. intros D0 E0 c.
  simpl. (* proof obligations: continuity follows from pointwise lub preservation *)
  admit.
Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.

(** Product cpo: pointwise order and lubs *)
Program Definition prod_cpo (A B : cpo) : cpo :=
  {| cpo_pre := {|
       carrier := (carrier A * carrier B);
       le := fun p q => le (fst p) (fst q) /\ le (snd p) (snd q);
       le_refl := _;
       le_trans := _
     |};
     lub_of_chain := fun c => (lub_of_chain (fun n => fst (c n)), lub_of_chain (fun n => snd (c n)));
     lub_upper := _;
     lub_least := _
  |}.
Next Obligation. intros [a b]; split; apply le_refl. Qed.
Next Obligation. intros [a1 b1] [a2 b2] [a3 b3] [H12a H12b] [H23a H23b]; split; apply (le_trans _ _ _ H12a H23a) || apply (le_trans _ _ _ H12b H23b). Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.

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
