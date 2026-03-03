(*  Natural-Number Instances

    Three order-theoretic structures on [nat] and related types.

    §1  [nat] as a [PartialOrder].
        Order: the standard Peano [<=].  [nat] is NOT an ω-CPO under
        this order because the chain [0, 1, 2, …] has no supremum in
        [nat].  To get a CPO, use [discrete nat] (§2) or [nat_inf] (§3).

    §2  [discrete nat] as a [CPO].
        Inherited from the generic [discrete] instance in [Discrete.v]:
        order is propositional equality, chains are forced constant, and
        the supremum is [c.[0]].

    §3  [nat_inf] (ℕ ∪ {∞}) as a [PointedCPO].
        The one-point compactification of [nat].  Concretely, an
        inductive type [fin n | infty] with the extended ordering:
          [fin m ⊑ fin n  ↔  m ≤ n],  [fin _ ⊑ infty],  [infty ⊑ infty].
        Bottom element: [fin 0].
        Supremum: if the chain eventually stabilises at a finite value
        [fin v], the sup is [fin v]; otherwise [infty].
        The stabilisation decision uses classical excluded middle
        ([ClassicalEpsilon]), which is standard for domain theory.

    This is [src/instances/Nat.v].

    Imports:
      [src/structures/Order.v] — HasLe … PartialOrder, chain
      [src/structures/CPO.v]   — HasSup, IsCPO, CPO, HasBottom, IsPointed,
                                 PointedCPO
    Extra stdlib imports:
      [Arith], [PeanoNat], [Lia]         — arithmetic on [nat]
      [ClassicalEpsilon]                  — [excluded_middle_informative],
                                           [constructive_indefinite_description]
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO.
From Stdlib Require Import Arith PeanoNat Lia ClassicalEpsilon.


(* ================================================================== *)
(*  §1  [nat] as a PartialOrder                                       *)
(* ================================================================== *)

(*
    The standard Peano ordering [<=] makes [nat] a partial order.
    We do NOT register a CPO instance: the chain [0,1,2,…] has no
    finite supremum.  For a CPO on natural numbers, use [discrete nat]
    (flat domain) or [nat_inf] (ℕ∞).
*)

HB.instance Definition _ := HasLe.Build nat Nat.le.

Lemma nat_le_refl : forall x : nat, x ⊑ x.
Proof. 
    intro; apply Nat.le_refl. 
Qed.

Lemma nat_le_trans : forall x y z : nat, x ⊑ y -> y ⊑ z -> x ⊑ z.
Proof. 
    intros x y z; apply Nat.le_trans. 
Qed.

HB.instance Definition _ := IsPreorder.Build nat nat_le_refl nat_le_trans.

Lemma nat_le_antisym : forall x y : nat, x ⊑ y -> y ⊑ x -> x = y.
Proof. 
    intros x y; apply Nat.le_antisymm. 
Qed.

HB.instance Definition _ := IsPartialOrder.Build nat nat_le_antisym.

(* The HB [⊑] notation on [nat] agrees with stdlib [<=]. *)
Lemma nat_leE (m n : nat) : (m ⊑ n) = (m <= n).
Proof. 
    reflexivity. 
Qed.


(* ================================================================== *)
(*  §2  [discrete nat] as a CPO                                       *)
(* ================================================================== *)

(*
    By importing [Discrete.v], the type [discrete nat] is automatically
    a [CPO.type] with the equality order.  No extra code is needed here;
    this section just records the fact for documentation and for the
    examples file.

    To use: [From DomainTheory.Instances Require Import Discrete Nat.]
    Then [discrete nat : CPO.type] resolves by canonical inference.
*)


(* ================================================================== *)
(*  §3  [nat_inf] — ℕ ∪ {∞} as a PointedCPO                          *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(*  §3.1  Type and order                                              *)
(* ------------------------------------------------------------------ *)

Inductive nat_inf : Type :=
  | fin   : nat -> nat_inf
  | infty : nat_inf.

Definition nat_inf_le (x y : nat_inf) : Prop :=
  match x, y with
  | fin m, fin n => m <= n
  | fin _, infty => True
  | infty, fin _ => False
  | infty, infty => True
  end.

HB.instance Definition _ := HasLe.Build nat_inf nat_inf_le.

(* Transparent unfolding lemma, useful inside proofs. *)
Lemma nat_inf_leE (x y : nat_inf) : (x ⊑ y) = nat_inf_le x y.
Proof. reflexivity. Qed.

Lemma nat_inf_le_refl : forall x : nat_inf, x ⊑ x.
Proof. intros [n|]; rewrite nat_inf_leE; simpl; auto. Qed.

Lemma nat_inf_le_trans :
  forall x y z : nat_inf, x ⊑ y -> y ⊑ z -> x ⊑ z.
Proof.
    intros [m|] [n|] [p|] H1 H2;
    rewrite nat_inf_leE in *; simpl in *;
    auto; try contradiction.
    exact (Nat.le_trans _ _ _ H1 H2).
Qed.

HB.instance Definition _ :=
  IsPreorder.Build nat_inf nat_inf_le_refl nat_inf_le_trans.

Lemma nat_inf_le_antisym :
  forall x y : nat_inf, x ⊑ y -> y ⊑ x -> x = y.
Proof.
  intros [m|] [n|] H1 H2;
  rewrite nat_inf_leE in *; simpl in *;
  auto; try contradiction.
  f_equal. exact (Nat.le_antisymm _ _ H1 H2).
Qed.

HB.instance Definition _ :=
  IsPartialOrder.Build nat_inf nat_inf_le_antisym.

(* Convenience lemmas for [fin] and [infty]. *)
Lemma fin_le (m n : nat) : fin m ⊑ fin n <-> m <= n.
Proof. rewrite nat_inf_leE; simpl; tauto. Qed.

Lemma fin_le_infty (n : nat) : fin n ⊑ infty.
Proof. rewrite nat_inf_leE; simpl; auto. Qed.

Lemma infty_le (x : nat_inf) : infty ⊑ x -> x = infty.
Proof. destruct x; rewrite nat_inf_leE; simpl; [contradiction | auto]. Qed.


(* ------------------------------------------------------------------ *)
(*  §3.2  Auxiliary: bounded monotone nat sequences stabilise         *)
(* ------------------------------------------------------------------ *)

(*
    A monotone function [f : nat → nat] bounded by [N] eventually
    reaches a constant value.  Proof by strong induction on [N]:
    either [f] hits [S N] and stays there, or all values are [≤ N]
    and the induction hypothesis applies.

    This fact is the discrete analogue of the monotone convergence
    theorem for ℝ, restricted to ω-chains in ℕ.
*)
Lemma mono_bounded_nat_stabilizes (f : nat -> nat) (N : nat) :
  (forall m n, m <= n -> f m <= f n) ->
  (forall n, f n <= N) ->
  exists v k, forall m, k <= m -> f m = v.
Proof.
  revert f. induction N as [|N IH]; intros f Hmono Hbnd.
  - exists 0, 0. intros m _. specialize (Hbnd m). lia.
  - destruct (excluded_middle_informative (exists k, f k = S N))
      as [[k0 Hk0] | Hlt].
  + exists (S N), k0. intros m Hm.
    specialize (Hmono k0 m Hm). specialize (Hbnd m). lia.
  + apply IH with (f := f); auto.
    intros n. specialize (Hbnd n).
    assert (f n <> S N) by (intro Heq; apply Hlt; exists n; exact Heq).
    lia.
Qed.


(* ------------------------------------------------------------------ *)
(*  §3.3  Supremum                                                    *)
(* ------------------------------------------------------------------ *)

(*
    A chain in [nat_inf] _eventually stabilises at a finite value_ if
    there exist [v : nat] and [k : nat] such that [c.[m] = fin v] for
    all [m ≥ k].  When this holds, the sup is [fin v].  Otherwise
    (the chain contains [infty] or the finite part diverges) the sup
    is [infty].

    The case split uses [excluded_middle_informative] (from
    [ClassicalEpsilon]) and [constructive_indefinite_description]
    to extract the witness [v] from the existential.
*)

Definition eventually_fin (c : chain nat_inf) : Prop :=
  exists v : nat, exists k : nat, forall m, k <= m -> c.[m] = fin v.

Definition nat_inf_sup (c : chain nat_inf) : nat_inf.
Proof.
  destruct (excluded_middle_informative (eventually_fin c)) as [Hstab | Hnstab].
  - apply constructive_indefinite_description in Hstab as [v _].
    exact (fin v).
  - exact infty.
Defined.

HB.instance Definition _ := HasSup.Build nat_inf nat_inf_sup.


(* ------------------------------------------------------------------ *)
(*  §3.4  CPO axioms                                                  *)
(* ------------------------------------------------------------------ *)

(* If the chain eventually equals [fin v] after position [k],
   then every element of the chain is [⊑ fin v]. *)
Lemma eventually_fin_ub (c : chain nat_inf) (v k : nat) :
  (forall m, k <= m -> c.[m] = fin v) -> forall n, c.[n] ⊑ fin v.
Proof.
  intros Hstab n.
  rewrite nat_inf_leE.
  destruct (Nat.le_gt_cases k n) as [Hkn | Hnk].
  - rewrite (Hstab n Hkn). simpl. lia.
  - assert (Hle : c.[n] ⊑ c.[k]) by (apply ch_mono; lia).
    rewrite nat_inf_leE in Hle. rewrite (Hstab k (Nat.le_refl k)) in Hle.
    destruct (c.[n]); simpl in *; auto.
Qed.

(* If every element is [⊑ fin N], the chain eventually stabilises. *)
Lemma bounded_chain_stabilizes (c : chain nat_inf) (N : nat) :
  (forall n, exists m, c.[n] = fin m /\ m <= N) ->
  eventually_fin c.
Proof.
    intros Hbnd.
    assert (Hval : forall n, {m : nat | c.[n] = fin m /\ m <= N}).
    { 
      intro n. apply constructive_indefinite_description. exact (Hbnd n). 
    }
    set (val := fun n => proj1_sig (Hval n)).
    assert (Hval_eq : forall n, c.[n] = fin (val n)).
    { 
      intro n. unfold val. destruct (Hval n) as [m' [Hm' HmN']]. exact Hm'. 
    }
    assert (Hval_bnd : forall n, val n <= N).
    { 
      intro n. unfold val. destruct (Hval n) as [m' [Hm' HmN']]. exact HmN'. 
    }
    assert (Hval_mono : forall m n, m <= n -> val m <= val n).
    { 
      intros m0 n0 Hmn.
      assert (H := ch_mono c m0 n0 Hmn).
      rewrite nat_inf_leE in H. 
      rewrite !Hval_eq in H. simpl in H. exact H. 
    }
    destruct (mono_bounded_nat_stabilizes val N Hval_mono Hval_bnd)
    as [v [k0 Hk0]].
    exists v, k0.
    intros m Hm. rewrite Hval_eq. f_equal. exact (Hk0 m Hm).
Qed.

Lemma nat_inf_sup_upper :
  forall (c : chain nat_inf) (n : nat), c.[n] ⊑ ⊔ c.
Proof.
  intros c n.
  unfold sup; simpl. unfold nat_inf_sup.
  destruct (excluded_middle_informative (eventually_fin c)) as [Hstab | Hnstab].
  - destruct (constructive_indefinite_description _ Hstab) as [v [k Hk]].
    simpl. apply eventually_fin_ub with (k := k). exact Hk.
  - rewrite nat_inf_leE. destruct (c.[n]); simpl; auto.
Qed.

Lemma nat_inf_sup_least :
  forall (c : chain nat_inf) (x : nat_inf),
    (forall n, c.[n] ⊑ x) -> ⊔ c ⊑ x.
Proof.
  intros c x Hub.
  unfold sup; simpl. unfold nat_inf_sup.
  destruct (excluded_middle_informative (eventually_fin c)) as [Hstab | Hnstab].
  - destruct (constructive_indefinite_description _ Hstab) as [v [k Hk]].
    simpl.
    assert (Hfv : fin v ⊑ x).
    { 
      rewrite <- (Hk k (Nat.le_refl k)). apply Hub. 
    }
    exact Hfv.
  - destruct x as [N|].
    + exfalso. apply Hnstab.
      apply bounded_chain_stabilizes with (N := N).
      intro n. specialize (Hub n). rewrite nat_inf_leE in Hub.
      destruct (c.[n]) as [m|]; simpl in Hub.
      * exists m. split; auto.
      * contradiction.
    + rewrite nat_inf_leE. simpl. auto.
Qed.

HB.instance Definition _ :=
  IsCPO.Build nat_inf nat_inf_sup_upper nat_inf_sup_least.


(* ------------------------------------------------------------------ *)
(*  §3.5  Pointed: bottom = fin 0                                     *)
(* ------------------------------------------------------------------ *)

HB.instance Definition _ := HasBottom.Build nat_inf (fin 0).

Lemma nat_inf_bottom_least : forall x : nat_inf, ⊥ ⊑ x.
Proof. intros [n|]; rewrite nat_inf_leE; simpl; auto with arith. Qed.

HB.instance Definition _ := IsPointed.Build nat_inf nat_inf_bottom_least.


(* ================================================================== *)
(*  §4  Convenience lemmas                                            *)
(* ================================================================== *)

(* The sup of a constant-[fin v] chain is [fin v]. *)
Lemma nat_inf_sup_const (v : nat) (c : chain nat_inf) :
  (forall n, c.[n] = fin v) -> ⊔ c = fin v.
Proof.
  intros Hconst.
  unfold sup; simpl. unfold nat_inf_sup.
  destruct (excluded_middle_informative (eventually_fin c)) as [Hstab | Hnstab].
  - destruct (constructive_indefinite_description _ Hstab) as [v' [k Hk]].
    simpl. f_equal.
    assert (H := Hk k (Nat.le_refl k)). rewrite Hconst in H.
    injection H; auto.
  - exfalso. apply Hnstab. exists v, 0. intros m _. apply Hconst.
Qed.

(* The sup of a chain containing [infty] is [infty]. *)
Lemma nat_inf_sup_infty (c : chain nat_inf) (k : nat) :
  c.[k] = infty -> ⊔ c = infty.
Proof.
  intros Hk.
  unfold sup; simpl. unfold nat_inf_sup.
  destruct (excluded_middle_informative (eventually_fin c)) as [Hstab | Hnstab].
  - destruct (constructive_indefinite_description _ Hstab) as [v' [k' Hk']].
    exfalso.
    (* The chain is monotone: c.[k] = infty means c.[m] = infty for m >= k *)
    assert (Hinf : c.[Nat.max k k'] = infty).
    { 
      assert (Hle : c.[k] ⊑ c.[Nat.max k k']).
      { 
        apply ch_mono. apply Nat.le_max_l. 
      }
      rewrite nat_inf_leE in Hle. 
      rewrite Hk in Hle. simpl in Hle.
      destruct (c.[Nat.max k k']); [contradiction | reflexivity]. 
    }
    assert (Hfin := Hk' (Nat.max k k') (Nat.le_max_r k k')).
    congruence.
  - reflexivity.
Qed.

(* [fin] is an order-embedding. *)
Lemma fin_mono (m n : nat) : m <= n -> fin m ⊑ fin n.
Proof. intro H. rewrite nat_inf_leE. simpl. exact H. Qed.

(* [infty] is the top element. *)
Lemma infty_top (x : nat_inf) : x ⊑ infty.
Proof. destruct x; rewrite nat_inf_leE; simpl; auto. Qed.
