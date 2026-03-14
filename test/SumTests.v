(*  SumTests

    Unit tests for the separated sum CPO construction from
    [src/theory/Sums.v].

    Tests:
    - §1  sum_le — ordering of injections
    - §2  sum_sup — supremum for stable left/right chains
    - §3  Injections — cont_inl, cont_inr
    - §4  sum_case — copairing computation and universal property
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory CPOTheory Sums.
From DomainTheory.Instances Require Import Nat Function.

From Stdlib Require Import Lia.


(* ================================================================== *)
(* §1  sum_le — ordering of injections                                 *)
(* ================================================================== *)

Section SumLeTests.

(* inl a ⊑ inl a' iff a ⊑ a'. *)
Lemma test_sum_le_inl :
    (inl (fin 2) : nat_inf + nat_inf) ⊑ inl (fin 5).
Proof.
  apply (proj2 (sum_le_inl (fin 2) (fin 5))).
  apply (proj2 (fin_le 2 5)). lia.
Qed.

(* inr b ⊑ inr b' iff b ⊑ b'. *)
Lemma test_sum_le_inr :
    (inr (fin 3) : nat_inf + nat_inf) ⊑ inr (fin 7).
Proof.
  apply (proj2 (sum_le_inr (fin 3) (fin 7))).
  apply (proj2 (fin_le 3 7)). lia.
Qed.

(* inl and inr are incomparable. *)
Lemma test_sum_le_inl_inr :
    ~ (inl (fin 0) : nat_inf + nat_inf) ⊑ inr (fin 0).
Proof. exact (sum_le_inl_inr_false (fin 0) (fin 0)). Qed.

Lemma test_sum_le_inr_inl :
    ~ (inr (fin 0) : nat_inf + nat_inf) ⊑ inl (fin 0).
Proof. exact (sum_le_inr_inl_false (fin 0) (fin 0)). Qed.

(* Reflexivity. *)
Lemma test_sum_le_refl :
    (inl (fin 3) : nat_inf + nat_inf) ⊑ inl (fin 3).
Proof. apply sum_le_refl. Qed.

End SumLeTests.


(* ================================================================== *)
(* §2  sum_sup — supremum of stable chains                             *)
(* ================================================================== *)

Open Scope type_scope.
Section SumSupTests.

(*
    A constant left chain has supremum = inl (sup of extracted chain).
*)

Lemma const_inl_chain_mono :
    forall m n : nat, m <= n ->
    (inl (fin 4) : nat_inf + nat_inf) ⊑ inl (fin 4).
Proof. intros. apply sum_le_refl. Qed.

Definition const_inl_chain : chain (nat_inf + nat_inf) :=
  Build_chain (fun _ => inl (fin 4)) const_inl_chain_mono.

Lemma test_sum_sup_inl :
    exists d, ⊔ const_inl_chain = inl d.
Proof.
  pose proof (sup_sum_inl const_inl_chain (fin 4) eq_refl
    : ⊔ const_inl_chain = inl (⊔ (map_chain (extract_left_mfun (D:=nat_inf) (E:=nat_inf) (fin 4)) const_inl_chain))) as H.
  eexists. exact H.
Qed.

(*
    A constant right chain has supremum = inr (sup of extracted chain).
*)

Lemma const_inr_chain_mono :
    forall m n : nat, m <= n ->
    (inr (fin 7) : nat_inf + nat_inf) ⊑ inr (fin 7).
Proof. intros. apply sum_le_refl. Qed.

Definition const_inr_chain : chain (nat_inf + nat_inf) :=
  Build_chain (fun _ => inr (fin 7)) const_inr_chain_mono.

Lemma test_sum_sup_inr :
    exists e, ⊔ const_inr_chain = inr e.
Proof.
  pose proof (sup_sum_inr const_inr_chain (fin 7) eq_refl
    : ⊔ const_inr_chain = inr (⊔ (map_chain (extract_right_mfun (D:=nat_inf) (E:=nat_inf) (fin 7)) const_inr_chain))) as H.
  eexists. exact H.
Qed.

End SumSupTests.


(* ================================================================== *)
(* §3  Injections — cont_inl, cont_inr                                *)
(* ================================================================== *)

Section InjectionTests.

(* cont_inl computation. *)
Lemma test_cont_inl_compute :
    (ι₁ : [nat_inf →c (nat_inf + nat_inf)]) (fin 3) = inl (fin 3).
Proof. reflexivity. Qed.

(* cont_inr computation. *)
Lemma test_cont_inr_compute :
    (ι₂ : [nat_inf →c (nat_inf + nat_inf)]) (fin 7) = inr (fin 7).
Proof. reflexivity. Qed.

(* cont_inl is continuous. *)
Lemma test_cont_inl_continuous :
    continuous (cf_mono (ι₁ (D := nat_inf) (E := nat_inf))).
Proof. exact (cf_cont ι₁). Qed.

(* cont_inr is continuous. *)
Lemma test_cont_inr_continuous :
    continuous (cf_mono (ι₂ (D := nat_inf) (E := nat_inf))).
Proof. exact (cf_cont ι₂). Qed.

End InjectionTests.


(* ================================================================== *)
(* §4  sum_case — copairing computation and universal property         *)
(* ================================================================== *)

Section SumCaseTests.

(* Test functions: id on nat_inf for both branches. *)
Definition f_left  : [nat_inf →c nat_inf] := cont_id nat_inf.
Definition f_right : [nat_inf →c nat_inf] := cont_const (fin 0).

(* sum_case_inl: sum_case f g (inl a) = f a. *)
Lemma test_sum_case_inl :
    sum_case f_left f_right (inl (fin 5)) = fin 5.
Proof. exact (sum_case_inl f_left f_right (fin 5)). Qed.

(* sum_case_inr: sum_case f g (inr b) = g b. *)
Lemma test_sum_case_inr :
    sum_case f_left f_right (inr (fin 5)) = fin 0.
Proof. exact (sum_case_inr f_left f_right (fin 5)). Qed.

(* Universal property: sum_case f g ∘ inl = f. *)
Lemma test_sum_case_comp_inl :
    cont_comp (sum_case f_left f_right) ι₁ = f_left.
Proof. exact (sum_case_comp_inl f_left f_right). Qed.

(* Universal property: sum_case f g ∘ inr = g. *)
Lemma test_sum_case_comp_inr :
    cont_comp (sum_case f_left f_right) ι₂ = f_right.
Proof. exact (sum_case_comp_inr f_left f_right). Qed.

(* Eta rule: h = sum_case (h ∘ inl) (h ∘ inr). *)
Lemma test_sum_case_eta (h : [(nat_inf + nat_inf) →c nat_inf]) :
    h = sum_case (cont_comp h ι₁) (cont_comp h ι₂).
Proof. exact (sum_case_eta h). Qed.

(* Uniqueness. *)
Lemma test_sum_case_unique
    (f : [nat_inf →c nat_inf]) (g : [nat_inf →c nat_inf])
    (h : [(nat_inf + nat_inf) →c nat_inf]) :
    cont_comp h ι₁ = f -> cont_comp h ι₂ = g -> h = sum_case f g.
Proof. exact (sum_case_unique f g h). Qed.

End SumCaseTests.
Close Scope type_scope.