(*  ProductTests

    Unit tests for the product CPO construction from
    [src/theory/Products.v].

    Tests:
    - §1  prod_le — ordering of pairs
    - §2  prod_sup — supremum computation
    - §3  Projections — pi1, pi2 continuity and computation
    - §4  Pairing — cont_pair computation and universal property
    - §5  Pointed product — bottom element
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory CPOTheory Products.
From DomainTheory.Instances Require Import Nat.

From Stdlib Require Import Lia.


(* ================================================================== *)
(* §1  prod_le — ordering of pairs                                     *)
(* ================================================================== *)

Section ProdLeTests.

(* (fin 2, fin 3) ⊑ (fin 5, fin 7) — both components ordered. *)
Lemma test_prod_le_concrete :
    ((fin 2, fin 3) : nat_inf * nat_inf) ⊑ (fin 5, fin 7).
Proof.
  apply (proj2 (prod_le_iff _ _)). split.
  - apply (proj2 (fin_le 2 5)). lia.
  - apply (proj2 (fin_le 3 7)). lia.
Qed.

(* (fin 5, fin 3) is NOT ⊑ (fin 2, fin 7). *)
Lemma test_prod_le_neg :
    ~ ((fin 5, fin 3) : nat_inf * nat_inf) ⊑ (fin 2, fin 7).
Proof.
  intro H. apply (proj1 (prod_le_iff _ _)) in H.
  destruct H as [H1 _].
  apply (proj1 (fin_le 5 2)) in H1. lia.
Qed.

(* Reflexivity. *)
Lemma test_prod_le_refl :
    ((fin 3, fin 4) : nat_inf * nat_inf) ⊑ (fin 3, fin 4).
Proof.
  apply prod_le_refl.
Qed.

(* prod_le_iff round-trip. *)
Lemma test_prod_le_iff :
    forall (p q : nat_inf * nat_inf),
    p ⊑ q <-> fst p ⊑ fst q /\ snd p ⊑ snd q.
Proof. intros. exact (prod_le_iff p q). Qed.

End ProdLeTests.


(* ================================================================== *)
(* §2  prod_sup — supremum of a chain of pairs                        *)
(* ================================================================== *)


Open Scope type_scope.
Section ProdSupTests.

(* A constant chain of pairs has sup equal to that pair. *)
Lemma test_prod_sup_const :
    ⊔ (const_chain ((fin 3, fin 4) : nat_inf * nat_inf)) = (fin 3, fin 4).
Proof. exact (prod_sup_const (fin 3, fin 4)). Qed.

(* The sup of a product chain projects to the sup of each component. *)
Lemma test_prod_sup_fst (c : chain (nat_inf * nat_inf)) :
    fst (⊔ c) = ⊔ (map_chain (fst_mono (D:=nat_inf) (E:=nat_inf)) c).
Proof. exact (prod_sup_fst c). Qed.

Lemma test_prod_sup_snd (c : chain (nat_inf * nat_inf)) :
    snd (⊔ c) = ⊔ (map_chain (snd_mono (D:=nat_inf) (E:=nat_inf)) c).
Proof. exact (prod_sup_snd c). Qed.

End ProdSupTests.


(* ================================================================== *)
(* §3  Projections — pi1 and pi2                                       *)
(* ================================================================== *)

Section ProjectionTests.

(* pi1 computation. *)
Lemma test_pi1_compute :
    (π₁ : [(nat_inf * nat_inf) →c nat_inf]) (fin 3, fin 7) = fin 3.
Proof. reflexivity. Qed.

(* pi2 computation. *)
Lemma test_pi2_compute :
    (π₂ : [(nat_inf * nat_inf) →c nat_inf]) (fin 3, fin 7) = fin 7.
Proof. reflexivity. Qed.

(* pi1 is continuous. *)
Lemma test_pi1_continuous :
    continuous (cf_mono (π₁ (D := nat_inf) (E := nat_inf))).
Proof. exact (cf_cont π₁). Qed.

(* pi2 is continuous. *)
Lemma test_pi2_continuous :
    continuous (cf_mono (π₂ (D := nat_inf) (E := nat_inf))).
Proof. exact (cf_cont π₂). Qed.

End ProjectionTests.


(* ================================================================== *)
(* §4  Pairing — cont_pair and universal property                      *)
(* ================================================================== *)

Section PairingTests.

(* cont_pair computation: ⟨f, g⟩ x = (f x, g x). *)
Lemma test_cont_pair_compute :
    (⟨ π₁, π₂ ⟩ : [(nat_inf * nat_inf) →c (nat_inf * nat_inf)])
      (fin 3, fin 7) = (fin 3, fin 7).
Proof.
  reflexivity.
Qed.

(* Universal property: pi1 ∘ ⟨f, g⟩ = f. *)
Lemma test_cont_pair_fst :
    forall (f : [nat_inf →c nat_inf]) (g : [nat_inf →c nat_inf]),
    cont_comp π₁ ⟨f, g⟩ = f.
Proof. intros. exact (cont_pair_fst f g). Qed.

(* Universal property: pi2 ∘ ⟨f, g⟩ = g. *)
Lemma test_cont_pair_snd :
    forall (f : [nat_inf →c nat_inf]) (g : [nat_inf →c nat_inf]),
    cont_comp π₂ ⟨f, g⟩ = g.
Proof. intros. exact (cont_pair_snd f g). Qed.

(* ⟨pi1, pi2⟩ = id. *)
Lemma test_cont_pair_id :
    (⟨ π₁, π₂ ⟩ : [(nat_inf * nat_inf) →c (nat_inf * nat_inf)]) =
    cont_id (nat_inf * nat_inf).
Proof. exact cont_pair_id. Qed.

(* Eta rule: h = ⟨pi1 ∘ h, pi2 ∘ h⟩. *)
Lemma test_cont_pair_eta (h : [nat_inf →c (nat_inf * nat_inf)]) :
    h = ⟨cont_comp π₁ h, cont_comp π₂ h⟩.
Proof. exact (cont_pair_eta h). Qed.

End PairingTests.


(* ================================================================== *)
(* §5  Pointed product — bottom element                                *)
(* ================================================================== *)

Section PointedTests.

(* Bottom of a product is (bot, bot). *)
Lemma test_prod_bottom :
    (⊥ : nat_inf * nat_inf) = ((⊥ : nat_inf), (⊥ : nat_inf)).
Proof. exact prod_bottom_eq. Qed.

(* fst bot = bot. *)
Lemma test_fst_bottom :
    fst (⊥ : nat_inf * nat_inf) = (⊥ : nat_inf).
Proof. exact fst_bottom. Qed.

(* snd bot = bot. *)
Lemma test_snd_bottom :
    snd (⊥ : nat_inf * nat_inf) = (⊥ : nat_inf).
Proof. exact snd_bottom. Qed.

(* bot ⊑ everything. *)
Lemma test_prod_bottom_least (p : nat_inf * nat_inf) :
    (⊥ : nat_inf * nat_inf) ⊑ p.
Proof. 
  destruct p; split; apply @bottom_least.
Qed.

End PointedTests.
Close Scope type_scope.