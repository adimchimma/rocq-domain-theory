(*  EnrichedTests

    Unit tests for the CPO-enriched category structure from
    [src/structures/Enriched.v] and [src/theory/EnrichedTheory.v],
    instantiated on the self-enriched category [CPO.type] from
    [src/instances/Function.v].

    Tests:
    - §1  Enriched composition — identity and associativity laws
    - §2  Composition continuity — left and right continuity
    - §3  EP-pairs — retraction and deflation
    - §4  Locally continuous functors — identity functor laws
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Theory Require Import OrderTheory CPOTheory Products
                                        FunctionSpaces EnrichedTheory.
From DomainTheory.Instances Require Import Discrete Nat Function.

From Stdlib Require Import Lia.


(* ================================================================== *)
(* §1  Enriched composition — identity and associativity               *)
(* ================================================================== *)
(*
    In the self-enriched category [CPO.type]:
      hom A B  =  [A →c B]
      id_mor A =  cont_id A
      f ⊚ g   =  cont_comp f g
*)

Section CompTests.
Context {C : CPOEnrichedCat.type}.
Variables (A B D : C).

(* Left identity: id ⊚ f = f. *)
Lemma test_comp_id_l (f : hom A B) :
    id_mor B ⊚ f = f.
Proof. apply comp_id_l. Qed.

(* Right identity: f ⊚ id = f. *)
Lemma test_comp_id_r (f : hom A B) :
    f ⊚ id_mor A = f.
Proof. apply comp_id_r. Qed.

(* Associativity: (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f). *)
Lemma test_comp_assoc
    (h : hom B D) (g : hom A B) (f : hom A A) :
    (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f).
Proof. apply comp_assoc. Qed.

End CompTests.

(* Concrete composition on CPO.type (self-enriched). *)
Section CompConcreteTests.

Lemma test_comp_concrete :
    (cont_const (fin 5) : [nat_inf →c nat_inf]) ∘
    (cont_const (fin 3) : [nat_inf →c nat_inf]) =
    cont_const (fin 5).
Proof.
  apply cont_fun_ext. intro x. reflexivity.
Qed.

End CompConcreteTests.


(* ================================================================== *)
(* §2  Composition continuity — left and right                         *)
(* ================================================================== *)

Section CompContTests.
Context {C : CPOEnrichedCat.type}.
Variables (A B D : C).

(* Left composition is continuous. *)
Lemma test_comp_cont_l (f : hom B D) :
    continuous (cf_mono (comp_l_cont_fun f (A := A))).
Proof. apply (cf_cont (comp_l_cont_fun f)). Qed.

(* Right composition is continuous. *)
Lemma test_comp_cont_r (g : hom A B) :
    continuous (cf_mono (comp_r_cont_fun g (B := D))).
Proof. apply (cf_cont (comp_r_cont_fun g)). Qed.

(* Left composition distributes over sup:
   f ⊚ (⊔ c) = ⊔ (map_chain (f ⊚ -) c). *)
Lemma test_comp_cont_l_eq
    (f : hom B D) (c : chain (hom A B)) :
    f ⊚ (⊔ c) = ⊔ (map_chain (cf_mono (comp_l_cont_fun f)) c).
Proof. apply (comp_cont_l_eq f c). Qed.

(* Right composition distributes over sup:
   (⊔ c) ⊚ g = ⊔ (map_chain (- ⊚ g) c). *)
Lemma test_comp_cont_r_eq
    (g : hom A B) (c : chain (hom B D)) :
    (⊔ c) ⊚ g = ⊔ (map_chain (cf_mono (comp_r_cont_fun g)) c).
Proof. apply (comp_cont_r_eq g c). Qed.

End CompContTests.


(* ================================================================== *)
(* §3  EP-pairs — retraction and deflation on CPO.type                 *)
(* ================================================================== *)

Section EPPairTests.
Context {C : CPOEnrichedCat.type}.
Variable (X : C).

(* The identity EP-pair: emb = proj = id. *)
Definition ep_id_X : ep_pair X X := ep_id X.

(* Retraction: proj ⊚ emb = id. *)
Lemma test_ep_retract :
    ep_proj ep_id_X ⊚ ep_emb ep_id_X = id_mor X.
Proof. apply (ep_proj_emb_retract ep_id_X). Qed.

(* Deflation: emb ⊚ proj ⊑ id. *)
Lemma test_ep_deflation :
    ep_emb ep_id_X ⊚ ep_proj ep_id_X ⊑ id_mor X.
Proof. apply (ep_deflation ep_id_X). Qed.

(* For the identity EP-pair, deflation is an equality. *)
Lemma test_ep_id_deflation_eq :
    ep_emb (ep_id X) ⊚ ep_proj (ep_id X) = id_mor X.
Proof. apply (ep_id_deflation_eq X). Qed.

(* Deflation is idempotent: (e ⊚ p) ⊚ (e ⊚ p) = e ⊚ p. *)
Lemma test_ep_deflation_idempotent :
    (ep_emb ep_id_X ⊚ ep_proj ep_id_X) ⊚
    (ep_emb ep_id_X ⊚ ep_proj ep_id_X) =
    ep_emb ep_id_X ⊚ ep_proj ep_id_X.
Proof. apply (ep_deflation_idempotent ep_id_X). Qed.

(* EP-pair composition: (id ∘ id) is still an EP-pair. *)
Definition ep_comp_id : ep_pair X X :=
  ep_comp ep_id_X ep_id_X.

Lemma test_ep_comp_retract :
    ep_proj ep_comp_id ⊚ ep_emb ep_comp_id = id_mor X.
Proof. apply (ep_retract ep_comp_id). Qed.

End EPPairTests.


(* ================================================================== *)
(* §4  Locally continuous functors — identity functor                  *)
(* ================================================================== *)

Section LCFunctorTests.
Context {C : CPOEnrichedCat.type}.
Variables (A B : C).

Definition id_lcf : lc_functor C := id_lc_functor C.

(* Object map is identity. *)
Lemma test_id_lcf_obj :
    lcf_obj id_lcf A = A.
Proof. apply (id_lcf_obj A). Qed.

(* Morphism map is identity. *)
Lemma test_id_lcf_mor (f : hom A B) :
    lcf_mor id_lcf A B f = f.
Proof. apply (id_lcf_mor f). Qed.

(* Composition: (id ∘ id) acts the same as id on morphisms. *)
Definition comp_id_id : lc_functor C :=
  comp_lc_functor id_lcf id_lcf.

Lemma test_comp_lcf_mor (f : hom A B) :
    lcf_mor comp_id_id A B f = f.
Proof.
  unfold comp_id_id.
  rewrite comp_lcf_mor.
  do 2 (rewrite <- id_lcf_mor). 
  reflexivity.
Qed.

(* Left identity: (id ∘ F).mor = F.mor. *)
Lemma test_comp_lcf_id_l (f : hom A B) :
    lcf_mor (comp_lc_functor id_lcf id_lcf) A B f =
    lcf_mor id_lcf A B f.
Proof. apply (comp_lcf_id_l id_lcf f). Qed.

(* Right identity: (F ∘ id).mor = F.mor. *)
Lemma test_comp_lcf_id_r (f : hom A B) :
    lcf_mor (comp_lc_functor id_lcf id_lcf) A B f =
    lcf_mor id_lcf A B f.
Proof. apply (comp_lcf_id_r id_lcf f). Qed.

End LCFunctorTests.
