(** Hierarchy-Builder instances

    This module demonstrates HB instances for algebraic and order structures.
    
    This module is part of the rocq-domain-theory project.
*)

From HB Require Import structures.
From Stdlib Require Import PeanoNat Arith.
From phase0_hierarchybuilder Require Import Hierarchies.

(** * Algebraic Instances *)

(** ** Natural numbers under addition *)

(** Natural numbers form a magma under addition *)
Fixpoint nat_add (n m : nat) : nat :=
    match n with
    | 0 => m
    | S n' => S (nat_add n' m)
    end.

HB.instance Definition nat_magma := hasOp.Build nat nat_add.

(** Addition is associative *)
Lemma nat_add_assoc : forall x y z, nat_add x (nat_add y z) = nat_add (nat_add x y) z.
Proof.
  induction x; intros y z.
  - reflexivity.
  - simpl. f_equal. apply IHx.
Qed.

HB.instance Definition nat_semigroup := 
  isAssociative.Build nat nat_add_assoc.

(** Addition has identity 0 *)
Lemma nat_add_0_l : forall x, nat_add 0 x = x.
Proof. reflexivity. Qed.

Lemma nat_add_0_r : forall x, nat_add x 0 = x.
Proof.
  induction x.
  - reflexivity.
  - simpl. f_equal. exact IHx.
Qed.

HB.instance Definition nat_monoid :=
  hasIdentity.Build nat 0 nat_add_0_l nat_add_0_r.

(** Addition is commutative *)
Lemma nat_add_S_r : forall n m, nat_add n (S m) = S (nat_add n m).
Proof.
  induction n; intro m.
  - reflexivity.
  - simpl. f_equal. apply IHn.
Qed.

Lemma nat_add_comm : forall x y, nat_add x y = nat_add y x.
Proof.
  induction x; intro y.
  - symmetry. apply nat_add_0_r.
  - simpl. rewrite nat_add_S_r. f_equal. apply IHx.
Qed.

HB.instance Definition nat_com_monoid :=
  isCommutative.Build nat nat_add_comm.

(** ** Natural numbers under multiplication *)

Definition nat_mul_type := nat.

HB.instance Definition nat_mul_magma := hasOp.Build nat_mul_type Nat.mul.
HB.instance Definition nat_mul_semigroup := 
  isAssociative.Build nat_mul_type Nat.mul_assoc.
HB.instance Definition nat_mul_monoid :=
  hasIdentity.Build nat_mul_type 1 Nat.mul_1_l Nat.mul_1_r.
HB.instance Definition nat_mul_com_monoid :=
  isCommutative.Build nat_mul_type Nat.mul_comm.

(** * Order-Theoretic Instances *)

(** ** Natural numbers with standard order *)

HB.instance Definition nat_preorder :=
  hasPreorder.Build nat Nat.le Nat.le_refl Nat.le_trans.

(** ** Unit type (trivial order) *)

HB.instance Definition unit_preorder :=
  hasPreorder.Build unit (fun _ _ => True) (fun _ => I) (fun _ _ _ _ _ => I).

(** ** Product preorders *)

Definition prod_le (A B : PreorderType.type) (p1 p2 : A * B) : Prop :=
  @le_op A (fst p1) (fst p2) /\ @le_op B (snd p1) (snd p2).

Lemma prod_le_refl (A B : PreorderType.type) : 
  forall p : A * B, prod_le A B p p.
Proof.
  intros [a b]. split; apply le_refl_ax.
Qed.

Lemma prod_le_trans (A B : PreorderType.type) :
  forall p q r : A * B, 
    prod_le A B p q -> prod_le A B q r -> prod_le A B p r.
Proof.
  intros [a1 b1] [a2 b2] [a3 b3] [H1 H2] [H3 H4].
  split; eapply le_trans_ax; eassumption.
Qed.

(** Note: Product preorder instance would require proper handling of PreorderType.sort *)
(* Commented out for now as it needs PreorderType.sort coercion *)
(* HB.instance Definition prod_preorder (A B : PreorderType.type) :=
  hasPreorder.Build (A * B) (prod_le A B) 
    (prod_le_refl A B) (prod_le_trans A B). *)

(** ** CPO Instances *)

(** Unit type is a CPO (trivial lubs) *)
Definition unit_lub (c : nat -> unit) : unit := tt.

Lemma unit_lub_upper : forall (c : nat -> unit),
  (forall m n, m <= n -> @le_op unit (c m) (c n)) ->
  forall n, @le_op unit (c n) (unit_lub c).
Proof. intros; exact I. Qed.

Lemma unit_lub_least : forall (c : nat -> unit) (x : unit),
  (forall m n, m <= n -> @le_op unit (c m) (c n)) ->
  (forall n, @le_op unit (c n) x) ->
  @le_op unit (unit_lub c) x.
Proof. intros; exact I. Qed.

HB.instance Definition unit_cpo :=
  hasCPO.Build unit unit_lub unit_lub_upper unit_lub_least.

(** Unit CPO is pointed *)
HB.instance Definition unit_pointed :=
  hasBottom.Build unit tt (fun _ => I).

(** * Verification Tests *)

(** Algebraic structure tests *)
Check nat : Magma.type.
Check nat : Semigroup.type.
Check nat : Monoid.type.
Check nat : ComMonoid.type.

Check nat_mul_type : Magma.type.
Check nat_mul_type : ComMonoid.type.

(** Order structure tests *)
Check nat : PreorderType.type.
Check unit : PreorderType.type.

(** CPO structure tests *)
Check unit : CPOType.type.
Check unit : PointedCPOType.type.

(** Test using operations *)
Example test_nat_add : @op nat 2 3 = 5.
Proof. reflexivity. Qed.

Example test_nat_le : @le_op nat 2 5.
Proof. repeat constructor. Qed.
