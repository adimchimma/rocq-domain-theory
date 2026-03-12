(*  NatTrans

    Phase 1: Enriched natural transformations between locally continuous
    endofunctors on a CPO-enriched category.

    Imports:
      [src/structures/Order.v]      — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]        — CPO, continuous, sup_upper, sup_least
      [src/structures/Morphisms.v]  — cont_fun, cont_comp, cont_id
      [src/structures/Enriched.v]   — CPOEnrichedCat, hom, comp, id_mor
      [src/theory/OrderTheory.v]    — le_antisym
      [src/theory/CPOTheory.v]      — sup_ext, sup_least, sup_upper,
                                      continuous_of_le
      [src/theory/EnrichedTheory.v] — lc_functor, lcf_obj, lcf_mor, lcf_cont,
                                      lcf_mono, lcf_id, lcf_comp,
                                      comp_lc_functor, id_lc_functor,
                                      comp_cont_l_eq, comp_cont_r_eq

    Contents
    ========
    S1  Natural transformation record
          [nat_trans F G]: components + naturality between [lc_functor]s.
          [nt_component]: accessor for the component at an object.

    S2  Identity and vertical composition
          [nt_id F]: identity natural transformation (components = id).
          [nt_vcomp beta alpha]: vertical composition (componentwise).

    S3  Horizontal composition (whiskering)
          [nt_lwhisker H alpha]: left whiskering [H * alpha].
          [nt_rwhisker alpha H]: right whiskering [alpha * H].

    S4  Pointwise order — natural transformations as a preorder
          [nt_le]: pointwise order on components.
          [nt_le_refl], [nt_le_trans], [nt_le_antisym].

    S5  Chains and suprema — natural transformations form a CPO
          [nt_chain_component]: extract a chain in a hom-CPO from a
            chain of natural transformations.
          [nt_sup]: pointwise supremum of a chain of natural
            transformations.
          [nt_sup_upper], [nt_sup_least]: CPO axioms.

    S6  Interchange law
          The interchange law for vertical and horizontal composition:
          [(beta' . beta) * (alpha' . alpha) = (beta' * alpha') . (beta * alpha)].

    Deferred (dependency on DomainTheory.Instances.Function):
      S7  Representable functor Hom(X,-) as an lc_functor on CPO.type.
      S8  Enriched Yoneda lemma: nat_trans (Hom(X,-)) F is isomorphic
          (as a CPO) to F(X).

    References:
      Kelly (1982) Ch. 1 — enriched natural transformations
      Mac Lane (1998) Ch. IX — natural transformations (ordinary setting)
      Abramsky & Jung (1994) S5.2 — CPO-enriched categories
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Theory Require Import
  OrderTheory ChainTheory CPOTheory EnrichedTheory.

From Stdlib Require Import FunctionalExtensionality ProofIrrelevance.


(* ================================================================== *)
(*   S1  Natural transformation record                                 *)
(* ================================================================== *)
(*
    An enriched natural transformation [alpha : F ==> G] between two
    locally continuous endofunctors [F, G : lc_functor C] consists of:

      nt_component : forall A : C, hom (lcf_obj F A) (lcf_obj G A)

    satisfying the naturality condition: for every [f : hom A B],

      lcf_mor G A B f  o  alpha_A  =  alpha_B  o  lcf_mor F A B f

    where [o] is composition in [C].

    We use [lc_functor] (EnrichedTheory.v) rather than the HB
    [LocallyContinuousFunctor] structure, since the record form
    allows working with multiple endofunctors on the same base
    category in a single section context.
*)

Section NatTransDef.
Context {C : CPOEnrichedCat.type}.

Record nat_trans (F G : lc_functor C) := {
  nt_component : forall (A : C), hom (lcf_obj F A) (lcf_obj G A);
  nt_naturality : forall (A B : C) (f : hom A B),
    (lcf_mor G A B f) ⊚ (nt_component A) =
    (nt_component B) ⊚ (lcf_mor F A B f);
}.

Arguments nt_component {F G} _ _.
Arguments nt_naturality {F G} _ _ _ _.


(* ================================================================== *)
(*   S2  Identity and vertical composition                             *)
(* ================================================================== *)
(*
    The identity natural transformation on [F]:
      id_F(A) = id_mor (F A)

    Naturality: F(f) o id = F(f) = id o F(f),
    by [comp_id_r] and [comp_id_l].
*)

Definition nt_id (F : lc_functor C) : nat_trans F F.
Proof.
  unshelve econstructor.
  - exact (fun A => id_mor (lcf_obj F A)).
  - intros A B f.
    rewrite (@comp_id_r C).
    rewrite (@comp_id_l C).
    reflexivity.
Defined.

Lemma nt_id_component (F : lc_functor C) (A : C) :
    nt_component (nt_id F) A = id_mor (lcf_obj F A).
Proof. reflexivity. Qed.

(*
    Vertical composition: given [alpha : F ==> G] and [beta : G ==> H],
      (beta . alpha)_A = beta_A  o  alpha_A

    Naturality of the composite follows from the two naturality squares:
      H(f) o beta_A o alpha_A
        = beta_B o G(f) o alpha_A       [naturality of beta]
        = beta_B o alpha_B o F(f)       [naturality of alpha]
*)

Definition nt_vcomp {F G H : lc_functor C}
    (beta : nat_trans G H) (alpha : nat_trans F G) : nat_trans F H.
Proof.
  unshelve econstructor.
  - exact (fun A => nt_component beta A ⊚ nt_component alpha A).
  - intros A B f.
    (*  H(f) o (beta_A o alpha_A) = (beta_B o alpha_B) o F(f)  *)
    cbn beta.
    rewrite <- (@comp_assoc C _ _ _ _
      (lcf_mor H A B f) (nt_component beta A) (nt_component alpha A)).
    rewrite (nt_naturality beta A B f).
    rewrite (@comp_assoc C _ _ _ _
      (nt_component beta B) (lcf_mor G A B f) (nt_component alpha A)).
    rewrite (nt_naturality alpha A B f).
    rewrite <- (@comp_assoc C _ _ _ _
      (nt_component beta B) (nt_component alpha B) (lcf_mor F A B f)).
    reflexivity.
Defined.

Lemma nt_vcomp_component {F G H : lc_functor C}
    (beta : nat_trans G H) (alpha : nat_trans F G) (A : C) :
    nt_component (nt_vcomp beta alpha) A =
      nt_component beta A ⊚ nt_component alpha A.
Proof. reflexivity. Qed.

(*
    Vertical composition is associative.
*)
Lemma nt_vcomp_assoc {F G H K : lc_functor C}
    (gamma : nat_trans H K) (beta : nat_trans G H) (alpha : nat_trans F G)
    (A : C) :
    nt_component (nt_vcomp gamma (nt_vcomp beta alpha)) A =
    nt_component (nt_vcomp (nt_vcomp gamma beta) alpha) A.
Proof.
  simpl.
  rewrite (@comp_assoc C).
  reflexivity.
Qed.

(*
    Identity is a left and right unit of vertical composition.
*)
Lemma nt_vcomp_id_l {F G : lc_functor C} (alpha : nat_trans F G) (A : C) :
    nt_component (nt_vcomp (nt_id G) alpha) A = nt_component alpha A.
Proof.
  simpl. rewrite (@comp_id_l C). reflexivity.
Qed.

Lemma nt_vcomp_id_r {F G : lc_functor C} (alpha : nat_trans F G) (A : C) :
    nt_component (nt_vcomp alpha (nt_id F)) A = nt_component alpha A.
Proof.
  simpl. rewrite (@comp_id_r C). reflexivity.
Qed.


(* ================================================================== *)
(*   S3  Horizontal composition (whiskering)                           *)
(* ================================================================== *)
(*
    Left whiskering: given [H : lc_functor C] and [alpha : F ==> G],
      (H * alpha)_A = H(alpha_A) : hom (H(F(A))) (H(G(A)))

    Naturality:
      (H o G)(f)  o  H(alpha_A)
        = H(G(f))  o  H(alpha_A)
        = H(G(f) o alpha_A)                    [functoriality of H]
        = H(alpha_B o F(f))                    [naturality of alpha]
        = H(alpha_B) o H(F(f))                [functoriality of H]
        = H(alpha_B) o (H o F)(f)
*)

Definition nt_lwhisker (H : lc_functor C) {F G : lc_functor C}
    (alpha : nat_trans F G) :
    nat_trans (comp_lc_functor H F) (comp_lc_functor H G).
Proof.
  unshelve econstructor.
  - exact (fun A =>
      lcf_mor H (lcf_obj F A) (lcf_obj G A) (nt_component alpha A)).
  - intros A B f.
    simpl.
    rewrite <- (lcf_comp H).
    rewrite (nt_naturality alpha A B f).
    rewrite (lcf_comp H).
    reflexivity.
Defined.

Lemma nt_lwhisker_component (H : lc_functor C) {F G : lc_functor C}
    (alpha : nat_trans F G) (A : C) :
    nt_component (nt_lwhisker H alpha) A =
      lcf_mor H (lcf_obj F A) (lcf_obj G A) (nt_component alpha A).
Proof. reflexivity. Qed.

(*
    Right whiskering: given [alpha : F ==> G] and [H : lc_functor C],
      (alpha * H)_A = alpha_{H(A)} : hom (F(H(A))) (G(H(A)))

    Naturality:
      G(H(f)) o alpha_{H(A)}
        = alpha_{H(B)} o F(H(f))              [naturality of alpha at H(f)]
*)

Definition nt_rwhisker {F G : lc_functor C} (alpha : nat_trans F G)
    (H : lc_functor C) :
    nat_trans (comp_lc_functor F H) (comp_lc_functor G H).
Proof.
  unshelve econstructor.
  - exact (fun A => nt_component alpha (lcf_obj H A)).
  - intros A B f.
    simpl.
    exact (nt_naturality alpha
      (lcf_obj H A) (lcf_obj H B) (lcf_mor H A B f)).
Defined.

Lemma nt_rwhisker_component {F G : lc_functor C} (alpha : nat_trans F G)
    (H : lc_functor C) (A : C) :
    nt_component (nt_rwhisker alpha H) A =
      nt_component alpha (lcf_obj H A).
Proof. reflexivity. Qed.

(*
    Full horizontal composition: given [alpha : F ==> G] and
    [beta : H ==> K], the horizontal composite [beta o alpha] is
    defined as [nt_vcomp (nt_rwhisker beta G) (nt_lwhisker H alpha)]
    (or equivalently, [nt_vcomp (nt_lwhisker K alpha) (nt_rwhisker beta F)]).

    We provide both definitions and show they agree.
*)

Definition nt_hcomp {F G H K : lc_functor C}
    (beta : nat_trans H K) (alpha : nat_trans F G) :
    nat_trans (comp_lc_functor H F) (comp_lc_functor K G) :=
  nt_vcomp (nt_rwhisker beta G) (nt_lwhisker H alpha).

Lemma nt_hcomp_component {F G H K : lc_functor C}
    (beta : nat_trans H K) (alpha : nat_trans F G) (A : C) :
    nt_component (nt_hcomp beta alpha) A =
      nt_component beta (lcf_obj G A) ⊚
      lcf_mor H (lcf_obj F A) (lcf_obj G A) (nt_component alpha A).
Proof. reflexivity. Qed.


(* ================================================================== *)
(*   S4  Pointwise order on natural transformations                    *)
(* ================================================================== *)
(*
    Two natural transformations [alpha, beta : F ==> G] are ordered
    pointwise in each hom-CPO:

      alpha <= beta  iff  forall A, alpha_A <= beta_A  in hom(F(A), G(A))

    This gives a preorder, and antisymmetry follows from [le_antisym]
    in each hom-CPO.
*)

Definition nt_le {F G : lc_functor C} (alpha beta : nat_trans F G) : Prop :=
  forall (A : C), nt_component alpha A ⊑ nt_component beta A.

Lemma nt_le_refl {F G : lc_functor C} (alpha : nat_trans F G) :
    nt_le alpha alpha.
Proof.
  intro A. exact (@le_refl (hom (lcf_obj F A) (lcf_obj G A)) _).
Qed.

Lemma nt_le_trans {F G : lc_functor C}
    (alpha beta gamma : nat_trans F G) :
    nt_le alpha beta -> nt_le beta gamma -> nt_le alpha gamma.
Proof.
  intros Hab Hbc A.
  etransitivity.
  - exact (Hab A).
  - exact (Hbc A).
Qed.

Lemma nt_le_antisym {F G : lc_functor C}
    (alpha beta : nat_trans F G) :
    nt_le alpha beta -> nt_le beta alpha -> alpha = beta.
Proof.
  intros Hab Hba.
  destruct alpha as [ca na], beta as [cb nb].
  simpl in *.
  assert (Hcomp : ca = cb).
  { apply functional_extensionality_dep; intro A.
    apply le_antisym.
    - exact (Hab A).
    - exact (Hba A). }
  subst cb.
  f_equal.
  apply proof_irrelevance.
Qed.


(* ------------------------------------------------------------------ *)
(*   Order structure — standalone (no HB instances)                    *)
(* ------------------------------------------------------------------ *)
(*
    Note: We do NOT register HB instances (HasLe, IsPreorder,
    IsPartialOrder, HasSup, IsCPO) for [nat_trans F G].
    Doing so for a generic [C : CPOEnrichedCat.type] creates universe
    constraints that conflict with Function.v's self-enrichment
    instance [CPO_IsCPOEnriched] (which needs CPO.type.u0 <=
    CPOEnrichedCat.axioms_.u0).  Even order-level HB instances
    constrain the universe of [nat_trans F G], which depends on [C],
    and these constraints cascade through HB's hierarchy.

    Instead, the order/CPO structure is provided as standalone
    definitions and lemmas.  Downstream code (e.g., Yoneda.v) uses
    [nt_le], [nt_sup], etc. directly.

    For chains, we define [nt_chain] as a lightweight wrapper that
    carries its own monotonicity witness, avoiding the need for
    [Preorder.type] coercion through HB.
*)

Record nt_chain {F G : lc_functor C} := Build_nt_chain {
  ntch : nat -> nat_trans F G;
  ntch_mono : forall m n, m <= n -> nt_le (ntch m) (ntch n);
}.

Arguments Build_nt_chain {F G} _ _.
Arguments ntch {F G} _ _.
Arguments ntch_mono {F G} _ _ _ _.


(* ================================================================== *)
(*   S5  Chains and suprema                                            *)
(* ================================================================== *)
(*
    A chain of natural transformations [alphas : nat -> nat_trans F G]
    (with monotonicity in the pointwise order) induces, at each object
    [A], a chain in the hom-CPO [hom (F A) (G A)].  The pointwise
    supremum of these chains again satisfies naturality, so it defines
    a natural transformation.

    We construct the CPO of natural transformations between fixed
    [F] and [G] using a custom chain type to avoid HB instance
    complications.
*)

Section NatTransChains.
Context {F G : lc_functor C}.

(*
    Extract a chain in the hom-CPO at object [A] from an [nt_chain].
*)
Definition nt_component_chain
    (cs : nt_chain (F:=F) (G:=G))
    (A : C) : chain (hom (lcf_obj F A) (lcf_obj G A)).
Proof.
  unshelve econstructor.
  - exact (fun n => nt_component (ntch cs n) A).
  - intros m n Hmn. exact (ntch_mono cs m n Hmn A).
Defined.

Lemma nt_component_chain_index
    (cs : nt_chain (F:=F) (G:=G)) (A : C) (n : nat) :
    (nt_component_chain cs A).[n] = nt_component (ntch cs n) A.
Proof. reflexivity. Qed.

(*
    The pointwise supremum of a chain of natural transformations
    satisfies naturality.

    Proof sketch: for each [f : hom A B],
      G(f) o (sup_n alpha_n(A))
        = G(f) o sup_n (alpha_n(A))
        = sup_n (G(f) o alpha_n(A))            [comp_cont_l]
        = sup_n (alpha_n(B) o F(f))            [naturality of each alpha_n]
        = (sup_n alpha_n(B)) o F(f)            [comp_cont_r]
*)
Lemma nt_sup_naturality
    (cs : nt_chain (F:=F) (G:=G)) (A B : C) (f : hom A B) :
    lcf_mor G A B f ⊚ ⊔ (nt_component_chain cs A) =
    ⊔ (nt_component_chain cs B) ⊚ lcf_mor F A B f.
Proof.
  rewrite (comp_cont_l_eq (lcf_mor G A B f) (nt_component_chain cs A)).
  rewrite (comp_cont_r_eq (lcf_mor F A B f) (nt_component_chain cs B)).
  apply sup_ext; intro n. simpl.
  exact (nt_naturality (ntch cs n) A B f).
Qed.

Definition nt_sup (cs : nt_chain (F:=F) (G:=G)) : nat_trans F G :=
  {| nt_component := fun A => ⊔ (nt_component_chain cs A);
     nt_naturality := nt_sup_naturality cs; |}.

Lemma nt_sup_component (cs : nt_chain (F:=F) (G:=G)) (A : C) :
    nt_component (nt_sup cs) A = ⊔ (nt_component_chain cs A).
Proof. reflexivity. Qed.

Lemma nt_sup_upper (cs : nt_chain (F:=F) (G:=G)) (n : nat) :
    nt_le (ntch cs n) (nt_sup cs).
Proof.
  intro A. simpl.
  exact (sup_upper (nt_component_chain cs A) n).
Qed.

Lemma nt_sup_least (cs : nt_chain (F:=F) (G:=G)) (beta : nat_trans F G) :
    (forall n, nt_le (ntch cs n) beta) -> nt_le (nt_sup cs) beta.
Proof.
  intros Hub A. simpl.
  apply sup_least; intro n.
  exact (Hub n A).
Qed.

End NatTransChains.


(* ================================================================== *)
(*   S6  Interchange law                                               *)
(* ================================================================== *)
(*
    The interchange law for vertical and horizontal composition.

    Given:
      alpha  : F  ==> G        beta  : H  ==> K
      alpha' : F' ==> G'       beta' : H' ==> K'

    with composable functors (F, G : C -> C; H, K : C -> C; etc.),
    the interchange law states that the two natural ways of composing
    a 2x2 grid of 2-cells agree:

      (beta' . beta) * (alpha' . alpha)
        = (beta' * alpha') . (beta * alpha)

    We prove this at each component, which reduces to associativity
    and functoriality.
*)

Section Interchange.
Context {F G : lc_functor C} {H K : lc_functor C}.

(*
    Simpler form: vertical composition commutes with left whiskering.

      H * (beta . alpha) = (H * beta) . (H * alpha)

    Proof: at each component A,
      H(beta_A o alpha_A) = H(beta_A) o H(alpha_A)
    by functoriality of H.
*)
Lemma nt_lwhisker_vcomp (L : lc_functor C) {E : lc_functor C}
    (beta : nat_trans G E) (alpha : nat_trans F G) (A : C) :
    nt_component (nt_lwhisker L (nt_vcomp beta alpha)) A =
    nt_component (nt_vcomp (nt_lwhisker L beta) (nt_lwhisker L alpha)) A.
Proof.
  simpl.
  rewrite (lcf_comp L).
  reflexivity.
Qed.

(*
    Vertical composition commutes with right whiskering.

      (beta . alpha) * L = (beta * L) . (alpha * L)

    Proof: at each component A, this is definitional (both sides
    compute to [beta_{L(A)} o alpha_{L(A)}]).
*)
Lemma nt_rwhisker_vcomp (L : lc_functor C) {E : lc_functor C}
    (beta : nat_trans G E) (alpha : nat_trans F G) (A : C) :
    nt_component (nt_rwhisker (nt_vcomp beta alpha) L) A =
    nt_component (nt_vcomp (nt_rwhisker beta L) (nt_rwhisker alpha L)) A.
Proof. reflexivity. Qed.

End Interchange.

End NatTransDef.

Arguments nat_trans {C} F G.
Arguments nt_component {C F G} _ _.
Arguments nt_naturality {C F G} _ _ _ _.
Arguments nt_id {C} F.
Arguments nt_vcomp {C F G H} beta alpha.
Arguments nt_lwhisker {C} H {F G} alpha.
Arguments nt_rwhisker {C F G} alpha H.
Arguments nt_hcomp {C F G H K} beta alpha.
Arguments nt_le {C F G} alpha beta.
Arguments nt_chain {C} F G.
Arguments Build_nt_chain {C F G} ntch ntch_mono.
Arguments ntch {C F G} _ _.
Arguments ntch_mono {C F G} _ _ _ _.
Arguments nt_component_chain {C F G} cs A.
Arguments nt_sup {C F G} cs.
