(*  enriched_usage -- Worked examples: CPO-enriched category structure.

    This file demonstrates the higher-level categorical constructions
    built on top of the basic CPO machinery.  Most examples use an
    abstract CPO-enriched category [C] with objects [A, B, D : C],
    showing that the toolkit works uniformly for any such category.
    The canonical example is the category of CPOs itself (registered
    in [Function.v]).

    Contents:
    - §1  CPO-enriched category -- hom-objects, composition, identity
    - §2  Composition continuity -- separate continuity of comp
    - §3  Locally continuous functor -- the representable Hom(X, -)
    - §4  Natural transformations -- identity, vertical composition
    - §5  Embedding-projection pairs -- retraction and deflation
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Instances Require Import Nat Function Yoneda.
From DomainTheory.Theory Require Import OrderTheory CPOTheory
                                        FunctionSpaces EnrichedTheory NatTrans.


(* ================================================================== *)
(*  §1  CPO-enriched category                                         *)
(* ================================================================== *)
(*
    A CPO-enriched category [C] has:
    - Objects [A, B, D : C]
    - Hom-CPOs [hom A B : CPO.type]   (each hom-set is a CPO)
    - Composition [f ⊚ g : hom A D]   (separately continuous)
    - Identity [id_mor A : hom A A]

    These satisfy the usual category laws:  left/right identity and
    associativity.  The enrichment axioms additionally require that
    composition is Scott-continuous in each argument.

    The canonical example: [CPO.type] forms a CPO-enriched category
    with [hom A B = [A →c B]], [⊚ = cont_comp], [id_mor = cont_id].
    This instance is registered in [Function.v].
*)

Section CategoryAxioms.
Context {C : CPOEnrichedCat.type}.
Variables (A B D : C).

(* Left identity:  id ⊚ f = f. *)
Example comp_id_l_demo (f : hom A B) :
    (id_mor B) ⊚ f = f.
Proof. apply comp_id_l. Qed.

(* Right identity:  f ⊚ id = f. *)
Example comp_id_r_demo (f : hom A B) :
    f ⊚ (id_mor A) = f.
Proof. apply comp_id_r. Qed.

(* Associativity:  (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f). *)
Example comp_assoc_demo (h : hom B D) (g : hom A B)
    (f : hom A A) :
    (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f).
Proof. apply comp_assoc. Qed.

End CategoryAxioms.


(* ================================================================== *)
(*  §2  Composition continuity                                        *)
(* ================================================================== *)
(*
    Enriched composition [⊚] is separately continuous in each argument:

    - Post-composition with a fixed [f : hom B D]:
          f ⊚ (⊔ gs) = ⊔_n (f ⊚ gs.[n])

    - Pre-composition with a fixed [g : hom A B]:
          (⊔ fs) ⊚ g = ⊔_n (fs.[n] ⊚ g)

    Joint continuity ([comp_joint_continuous]) states that [⊚] is
    continuous as a map from the product hom-CPO
    [hom A B * hom B D  →c  hom A D].
*)

Section CompContinuity.
Context {C : CPOEnrichedCat.type}.
Variables (A B D : C).

(* Post-composition with f is Scott-continuous. *)
Example comp_cont_l_demo (f : hom B D)
    (c : chain (hom A B)) :
    f ⊚ (⊔ c) = ⊔ (map_chain (cf_mono (comp_l_cont_fun f)) c).
Proof. exact (comp_cont_l_eq f c). Qed.

(* Pre-composition with g is Scott-continuous. *)
Example comp_cont_r_demo (g : hom A B)
    (c : chain (hom B D)) :
    (⊔ c) ⊚ g = ⊔ (map_chain (cf_mono (comp_r_cont_fun g)) c).
Proof. exact (comp_cont_r_eq g c). Qed.

End CompContinuity.


(* ================================================================== *)
(*  §3  Locally continuous functor -- Hom(X, -)                       *)
(* ================================================================== *)
(*
    A locally continuous (LC) functor is an endofunctor on a
    CPO-enriched category whose morphism action is a continuous map
    between hom-CPOs.

    [repr_functor X] from [Yoneda.v] is the covariant representable
    functor [Hom(X, -)] on the CPO-enriched category of CPOs:

        F_obj : A  ->  [X →c A]
        F_mor : f  ->  post-composition with f

    This witnesses [Hom(X, -)] as a locally continuous endofunctor.
    The [lc_functor] record (from [EnrichedTheory.v]) packages the
    object map, morphism map, and the functoriality + continuity proofs.
*)

Section ReprFunctorExamples.
Variable X : CPO.type.

Definition F := repr_functor X.

(* Object action: F maps A to [X →c A]. *)
Example repr_obj_demo (A : CPO.type) :
    lcf_obj F A = ([X →c A] : CPO.type).
Proof. exact (repr_functor_obj X A). Qed.

(* Identity preservation: F id = id. *)
Example repr_id_demo (A : CPO.type) :
    lcf_mor F A A (id_mor A) = id_mor (lcf_obj F A).
Proof. exact (lcf_id F A). Qed.

(* Composition preservation: F(g ⊚ f) = F(g) ⊚ F(f). *)
Example repr_comp_demo (A B D : CPO.type)
    (g : hom B D) (f : hom A B) :
    lcf_mor F A D (g ⊚ f) =
    (lcf_mor F B D g) ⊚ (lcf_mor F A B f).
Proof. exact (lcf_comp F A B D g f). Qed.

End ReprFunctorExamples.


(* ================================================================== *)
(*  §4  Natural transformations                                       *)
(* ================================================================== *)
(*
    A natural transformation [alpha : F => G] between LC functors
    on a CPO-enriched category consists of a family of morphisms
    [alpha_A : hom (F A) (G A)] satisfying the naturality square:

        G f ⊚ alpha_A = alpha_B ⊚ F f

    Natural transformations carry a pointwise order and admit
    pointwise suprema (from the hom-CPO structure).
*)

Section NatTransExamples.
Variable X : CPO.type.

Let F0 := repr_functor X.

(* The identity natural transformation on F0. *)
Definition alpha_id := nt_id F0.

(* Its component at any object is the identity morphism. *)
Example nt_id_component_demo (A : CPO.type) :
    nt_component alpha_id A = id_mor (lcf_obj F0 A).
Proof. exact (nt_id_component F0 A). Qed.

(* Natural transformations carry a pointwise order. *)
Example nt_le_refl_demo : nt_le alpha_id alpha_id.
Proof. exact (nt_le_refl alpha_id). Qed.

(* Vertical composition: (beta . alpha)_A = beta_A ⊚ alpha_A. *)
Example nt_vcomp_demo (alpha beta : nat_trans F0 F0) (A : CPO.type) :
    nt_component (nt_vcomp beta alpha) A =
    (nt_component beta A) ⊚ (nt_component alpha A).
Proof. exact (nt_vcomp_component beta alpha A). Qed.

End NatTransExamples.


(* ================================================================== *)
(*  §5  Embedding-projection pairs                                    *)
(* ================================================================== *)
(*
    An EP-pair [(e, p) : ep_pair A B] in a CPO-enriched category
    consists of:
    - an embedding  [e : hom A B]
    - a projection  [p : hom B A]

    satisfying:
    - retraction:  [p ⊚ e = id_A]   (round-trip through B recovers A)
    - deflation:   [e ⊚ p <= id_B]  (the composition is below identity)

    The deflation [e ⊚ p] is an idempotent below the identity -- it
    "approximates" the identity on B.  Chains of EP-pairs are the
    input to the bilimit construction for solving recursive domain
    equations (see [recursive_domain.v]).
*)

Section EPPairExamples.
Context {C : CPOEnrichedCat.type}.
Variable A : C.

(* The identity EP-pair: both embedding and projection are id. *)
Definition ep := ep_id A.

(* Retraction: proj ⊚ emb = id. *)
Example ep_retract_demo :
    ep_proj ep ⊚ ep_emb ep = id_mor A.
Proof. exact (ep_retract ep). Qed.

(* Deflation: emb ⊚ proj <= id. *)
Example ep_deflation_demo :
    ep_emb ep ⊚ ep_proj ep ⊑ id_mor A.
Proof. exact (ep_deflation ep). Qed.

(* For the identity EP, the deflation is actually an equality. *)
Example ep_id_eq_demo :
    ep_emb ep ⊚ ep_proj ep = id_mor A.
Proof. exact (ep_id_deflation_eq A). Qed.

(* The deflation is idempotent:  (e ⊚ p) ⊚ (e ⊚ p) = e ⊚ p. *)
Example ep_idem_demo :
    (ep_emb ep ⊚ ep_proj ep) ⊚ (ep_emb ep ⊚ ep_proj ep)
    = ep_emb ep ⊚ ep_proj ep.
Proof. exact (ep_deflation_idempotent ep). Qed.

End EPPairExamples.
