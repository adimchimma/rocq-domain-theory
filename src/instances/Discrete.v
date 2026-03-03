(*  Discrete CPO Instances

    Two basic CPO constructions that serve as building blocks throughout
    the library.

    §1  [unit] as a pointed CPO.
        Order: [fun _ _ => True].  Every chain supremum is [tt].
        Bottom: [tt].

    §2  [discrete A] — the equality-ordered CPO on any type [A].
        A newtype wrapper [discrete A := A] carries the order
        [x ⊑ y  ↔  x = y].  Monotone chains are forced to be constant,
        so [⊔ c = c.[0]].  No bottom element in general; apply [Lift]
        to obtain a pointed domain.

    This is [src/instances/Discrete.v].

    Imports:
      [src/structures/Order.v] — HasLe … PartialOrder, chain
      [src/structures/CPO.v]   — HasSup, IsCPO, CPO, HasBottom, IsPointed, PointedCPO
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO.


(* ================================================================== *)
(*  §1  Unit CPO                                                      *)
(* ================================================================== *)

(*
    The order on [unit] is trivially [True]: every pair is related.
    This makes [unit] a one-element partial order — the terminal object
    in the category of CPOs.
*)

HB.instance Definition unit_hasLe :=
  HasLe.Build unit (fun _ _ => True).

HB.instance Definition unit_isPreorder :=
  IsPreorder.Build unit (fun _ => I) (fun _ _ _ _ _ => I).

Lemma unit_le_antisym : forall (x y : unit), x ⊑ y -> y ⊑ x -> x = y.
Proof. 
    intros [] [] _ _; reflexivity. 
Qed.

HB.instance Definition unit_isPartialOrder :=
  IsPartialOrder.Build unit unit_le_antisym.

(* Every chain in [unit] has supremum [tt]. *)
HB.instance Definition unit_hasSup :=
  HasSup.Build unit (fun _ => tt).

Lemma unit_sup_upper : forall (c : chain unit) (n : nat), c.[n] ⊑ ⊔ c.
Proof. 
    intros; exact I. 
Qed.

Lemma unit_sup_least : forall (c : chain unit) (x : unit),
  (forall n, c.[n] ⊑ x) -> ⊔ c ⊑ x.
Proof. 
    intros c [] _; exact I. 
Qed.

HB.instance Definition unit_isCPO :=
  IsCPO.Build unit unit_sup_upper unit_sup_least.

(* [unit] is pointed with bottom element [tt]. *)
HB.instance Definition unit_hasBottom :=
  HasBottom.Build unit tt.

HB.instance Definition unit_isPointed :=
  IsPointed.Build unit (fun _ => I).

(* Convenience: the supremum is always [tt]. *)
Lemma unit_sup_tt (c : chain unit) : ⊔ c = tt.
Proof. 
    destruct (⊔ c); reflexivity. 
Qed.


(* ================================================================== *)
(*  §2  Discrete CPO                                                  *)
(* ================================================================== *)

(*
    The [discrete] wrapper: a newtype around [A] so that HB registers
    the equality order on [discrete A] without polluting every type
    with a global instance.

    Notation convention: we keep plain [discrete] as a Definition rather
    than an Inductive so that [discrete A] computes to [A] and coercions
    are trivial.
*)
Definition discrete (A : Type) : Type := A.

Definition to_discrete   {A : Type} (a : A) : discrete A := a.
Definition from_discrete {A : Type} (d : discrete A) : A  := d.

Section DiscreteInstances.
Variable A : Type.

(* Order: propositional equality *)
HB.instance Definition _ := HasLe.Build (discrete A) (fun x y => x = y).

Lemma discrete_le_refl : forall x : discrete A, x ⊑ x.
Proof. 
    intro; reflexivity. 
Qed.

Lemma discrete_le_trans :
  forall x y z : discrete A, x ⊑ y -> y ⊑ z -> x ⊑ z.
Proof. 
    exact (@eq_trans (discrete A)). 
Qed.

HB.instance Definition _ :=
    IsPreorder.Build (discrete A) discrete_le_refl discrete_le_trans.

Lemma discrete_le_antisym :
    forall x y : discrete A, x ⊑ y -> y ⊑ x -> x = y.
Proof. 
    intros x y Hxy _. exact Hxy. 
Qed.

HB.instance Definition _ :=
    IsPartialOrder.Build (discrete A) discrete_le_antisym.

(* Chains are constant *)

Lemma discrete_chain_const (c : chain (discrete A)) :
    forall n, c.[n] = c.[0].
Proof.
    intro n. symmetry.
    apply (@ch_mono (discrete A) c).
    exact (le_0_n n).
Qed.

(* Supremum: return c.[0] *)
Definition discrete_sup (c : chain (discrete A)) : discrete A := c.[0].

HB.instance Definition _ := HasSup.Build (discrete A) discrete_sup.

Lemma discrete_sup_upper :
    forall (c : chain (discrete A)) (n : nat), c.[n] ⊑ ⊔ c.
Proof.
    intros c n. unfold sup. simpl. unfold discrete_sup.
    exact (discrete_chain_const c n).
Qed.

Lemma discrete_sup_least :
    forall (c : chain (discrete A)) (x : discrete A),
        (forall n, c.[n] ⊑ x) -> ⊔ c ⊑ x.
Proof.
    intros c x Hub. unfold sup. simpl. unfold discrete_sup.
    exact (Hub 0).
Qed.

HB.instance Definition _ :=
  IsCPO.Build (discrete A) discrete_sup_upper discrete_sup_least.

End DiscreteInstances.


(* ================================================================== *)
(*  §3  Convenience lemmas                                            *)
(* ================================================================== *)

(* The order on [discrete A] is definitionally [eq]. *)
Lemma discrete_le_iff {A : Type} (x y : discrete A) :
  x ⊑ y <-> x = y.
Proof. 
    split; auto.
Qed.

(* Any two positions in a discrete chain agree. *)
Lemma discrete_chain_eq {A : Type} (c : chain (discrete A)) :
  forall m n, c.[m] = c.[n].
Proof.
  intros m n.
  transitivity (c.[0]).
  - exact (discrete_chain_const A c m).
  - symmetry. exact (discrete_chain_const A c n).
Qed.
