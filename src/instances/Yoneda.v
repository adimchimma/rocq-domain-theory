(*  Yoneda

    Phase 1: The representable functor Hom(X,-) as a locally continuous
    endofunctor on CPO.type, and the enriched Yoneda lemma.

    Imports:
      [src/structures/Order.v]       — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]         — CPO, continuous, sup_upper, sup_least
      [src/structures/Morphisms.v]   — cont_fun, cont_comp, cont_id
      [src/structures/Enriched.v]    — CPOEnrichedCat, hom, comp, id_mor
      [src/theory/OrderTheory.v]     — le_antisym
      [src/theory/CPOTheory.v]       — sup_ext, continuous_of_le
      [src/theory/FunctionSpaces.v]  — fun_le, fun_sup, sup_apply, fun_sup_apply
      [src/theory/EnrichedTheory.v]  — lc_functor, lcf_obj, lcf_mor, etc.
      [src/theory/NatTrans.v]        — nat_trans, nt_component, nt_naturality
      [src/instances/Function.v]     — CPO.type as CPOEnrichedCat,
                                       cont_postcomp, cont_ap, cont_const

    Contents
    ========
    S1  Representable functor Hom(X,-)
          [repr_functor X]: the covariant hom-functor as an [lc_functor]
          on [CPO.type].

    S2  Enriched Yoneda lemma
          [yoneda_eval]: nat_trans (repr_functor X) F -> lcf_obj F X
            Extract alpha_X(id_X).
          [yoneda_embed]: lcf_obj F X -> nat_trans (repr_functor X) F
            Given x : F(X), define alpha_A(f) = F(f)(x).
          [yoneda_eval_embed]: left inverse.
          [yoneda_embed_eval]: right inverse.
          [yoneda_eval_mono]: yoneda_eval is monotone.
          [yoneda_eval_cont]: yoneda_eval is continuous.
          [yoneda_embed_mono]: yoneda_embed is monotone.
          [yoneda_embed_cont]: yoneda_embed is continuous.
          [yoneda_iso]: the two maps form a CPO isomorphism.

    References:
      Kelly (1982) Ch. 2.4 — enriched Yoneda lemma
      Mac Lane (1998) Ch. III.2 — ordinary Yoneda lemma
      Abramsky & Jung (1994) S3.2, S5.2 — CPO-enrichment
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Theory Require Import
  OrderTheory ChainTheory CPOTheory FunctionSpaces EnrichedTheory NatTrans.
From DomainTheory.Instances Require Import Function.

From Stdlib Require Import FunctionalExtensionality ProofIrrelevance.


(* ================================================================== *)
(*   S1  Representable functor Hom(X,-)                                *)
(* ================================================================== *)
(*
    For a fixed CPO [X], the covariant hom-functor [Hom(X, -)] is the
    locally continuous endofunctor on [CPO.type] (viewed as a
    CPO-enriched category via [Function.v]) defined by:

      Object action:    D  |->  [X ->c D]
      Morphism action:  f : [A ->c B]  |->  cont_postcomp f : [[X ->c A] ->c [X ->c B]]

    This is the standard representable functor in the enriched setting.
    Local continuity of the morphism action means: for a chain
    [fs : chain [A ->c B]], post-composing with [sup fs] gives the sup
    of post-composing with each [fs.[n]].

    On [CPO.type], [hom A B = [A ->c B]], [id_mor A = cont_id A], and
    [f ⊚ g = cont_comp f g].
*)

Section ReprFunctor.
Context (X : CPO.type).

(*
    Morphism action: post-composition [f |-> f o -].
    This is [cont_postcomp f], which has type
      [[X ->c A] ->c [X ->c B]]
    when [f : [A ->c B]].

    On CPO.type, [hom A B] resolves to [cont_fun A B], so the morphism
    action has the right type for [lcf_mor].
*)

Definition repr_mor (A B : CPO.type) (f : hom A B) :
    hom ([X →c A] : CPO.type) ([X →c B] : CPO.type) :=
  cont_postcomp f.

Lemma repr_mor_mono (A B : CPO.type) :
    monotone (hom A B)
      (hom ([X →c A] : CPO.type) ([X →c B] : CPO.type))
      (repr_mor A B).
Proof.
  intros f1 f2 Hf g x. simpl.
  exact (Hf (g x)).
Qed.

Lemma repr_mor_cont (A B : CPO.type) :
    @continuous (hom A B)
      (hom ([X →c A] : CPO.type) ([X →c B] : CPO.type))
      (Build_mono_fun (repr_mor A B) (repr_mor_mono A B)).
Proof.
  intro fs.
  apply cont_fun_ext; intro g.
  simpl. unfold postcomp_fun. simpl.
  apply cont_fun_ext; intro x.
  unfold fun_sup_fun.
  apply sup_ext; intro n.
  reflexivity.
Qed.

Lemma repr_id (A : CPO.type) :
    repr_mor A A (id_mor A) =
      id_mor (([X →c A] : CPO.type) : CPOEnrichedCat.sort CPO.type).
Proof.
  apply cont_fun_ext; intro g.
  apply cont_fun_ext; intro x.
  reflexivity.
Qed.

Lemma repr_comp (A B D : CPO.type) (f : hom B D) (g : hom A B) :
    repr_mor A D (f ⊚ g) =
      (repr_mor B D f) ⊚ (repr_mor A B g).
Proof.
  apply cont_fun_ext; intro h.
  apply cont_fun_ext; intro x.
  reflexivity.
Qed.

Definition repr_functor : lc_functor CPO.type := {|
  lcf_obj  := fun D => [X →c D] : CPO.type;
  lcf_mor  := repr_mor;
  lcf_mono := repr_mor_mono;
  lcf_cont := repr_mor_cont;
  lcf_id   := repr_id;
  lcf_comp := repr_comp;
|}.

Lemma repr_functor_obj (D : CPO.type) :
    lcf_obj repr_functor D = ([X →c D] : CPO.type).
Proof. reflexivity. Qed.

Lemma repr_functor_mor (A B : CPO.type) (f : hom A B) (g : [X →c A]) :
    lcf_mor repr_functor A B f g = cont_comp f g.
Proof. reflexivity. Qed.

End ReprFunctor.

Arguments repr_functor X : clear implicits.


(* ================================================================== *)
(*   S2  Enriched Yoneda lemma                                         *)
(* ================================================================== *)
(*
    The enriched Yoneda lemma (Kelly 1982, Ch. 2.4) for CTR-enriched
    categories states that for a locally continuous functor [F] and
    an object [X]:

      nat_trans (repr_functor X) F  ≅  lcf_obj F X     (as a CPO)

    The isomorphism is:
      yoneda_eval  : alpha  |->  alpha_X (id_X)
      yoneda_embed : x      |->  (A |-> F_mor(f)(x))

    We prove:
    (a) These are inverse to each other.
    (b) Both directions are Scott-continuous.
    Together this establishes a CPO isomorphism.
*)

Section YonedaLemma.
Context (X : CPO.type) (F : lc_functor CPO.type).

(* ------------------------------------------------------------------ *)
(*   Evaluation direction: alpha |-> alpha_X(id_X)                     *)
(* ------------------------------------------------------------------ *)

Definition yoneda_eval (alpha : nat_trans (repr_functor X) F) :
    lcf_obj F X :=
  (nt_component alpha X : hom (lcf_obj (repr_functor X) X) (lcf_obj F X))
    (cont_id X).

(* ------------------------------------------------------------------ *)
(*   Embedding direction: x |-> (A |-> F_mor(f)(x))                    *)
(* ------------------------------------------------------------------ *)
(*
    Given [x : lcf_obj F X] and an object [A : CPO.type], we need to
    build a morphism:
      component_A : hom ([X ->c A]) (lcf_obj F A)
    i.e., a continuous function from [[X ->c A]] to [lcf_obj F A].

    For [f : [X ->c A]], the component is [lcf_mor F X A f x].
    This is the composite of applying [lcf_cont_fun F] (which is
    continuous) to [f], then evaluating at [x].
*)

Definition yoneda_component (x : lcf_obj F X) (A : CPO.type)
    (f : [X →c A]) : lcf_obj F A :=
  lcf_mor F X A f x.

Lemma yoneda_component_mono (x : lcf_obj F X) (A : CPO.type) :
    monotone ([X →c A]) (lcf_obj F A) (yoneda_component x A).
Proof.
  intros f1 f2 Hf. unfold yoneda_component.
  exact (lcf_mono F X A f1 f2 Hf x).
Qed.

Lemma yoneda_component_cont (x : lcf_obj F X) (A : CPO.type) :
    continuous (Build_mono_fun (yoneda_component x A)
                               (yoneda_component_mono x A)).
Proof.
  intro fs.
  pose proof (lcf_cont F X A fs) as H.
  unfold lcf_mono_fun in H. cbn [mf_fun] in H.
  unfold yoneda_component. cbn beta.
  etransitivity.
  { exact (f_equal (fun (h : [lcf_obj F X →c lcf_obj F A]) => h x) H). }
  apply sup_ext; intro n. reflexivity.
Qed.

Definition yoneda_component_fun (x : lcf_obj F X) (A : CPO.type) :
    hom ([X →c A] : CPO.type) (lcf_obj F A) :=
  Build_cont_fun
    (Build_mono_fun (yoneda_component x A) (yoneda_component_mono x A))
    (yoneda_component_cont x A).

(*
    Naturality of [yoneda_component_fun x]:
    For [g : [A ->c B]], we need:
      F(g) o (yoneda_component_fun x A)
        = (yoneda_component_fun x B) o repr_mor X A B g

    At a point [f : [X ->c A]]:
      LHS: F(g)(F(f)(x))
           = F(g o f)(x)           [functoriality of F]
      RHS: F(g o f)(x)             [definition of repr_mor and yoneda_component]
*)
Lemma yoneda_naturality (x : lcf_obj F X)
    (A B : CPO.type) (g : hom A B) :
    (lcf_mor F A B g) ⊚ (yoneda_component_fun x A) =
    (yoneda_component_fun x B) ⊚ (lcf_mor (repr_functor X) A B g).
Proof.
  apply cont_fun_ext; intro f.
  simpl. unfold yoneda_component.
  change (((lcf_mor F A B g) ⊚ (lcf_mor F X A f)) x =
          lcf_mor F X B (g ⊚ f) x).
  rewrite <- (lcf_comp F X A B g f).
  reflexivity.
Qed.

Definition yoneda_embed (x : lcf_obj F X) :
    nat_trans (repr_functor X) F.
Proof.
  unshelve econstructor.
  - exact (fun A => yoneda_component_fun x A).
  - intros A B g. exact (yoneda_naturality x A B g).
Defined.


(* ------------------------------------------------------------------ *)
(*   Round-trip identities                                             *)
(* ------------------------------------------------------------------ *)

(*
    eval (embed x) = x:
      embed(x)_X(id_X) = lcf_mor F X X (id_X) x = F(id)(x) = id(x) = x.
*)
Theorem yoneda_eval_embed (x : lcf_obj F X) :
    yoneda_eval (yoneda_embed x) = x.
Proof.
  unfold yoneda_eval.
  change (yoneda_component_fun x X (id_mor X) = x).
  unfold yoneda_component_fun, yoneda_component. simpl.
  (* lcf_mor F X X (id_mor X) x = x *)
  pose proof (lcf_id F X) as H.
  exact (f_equal (fun (h : [lcf_obj F X →c lcf_obj F X]) => h x) H).
Qed.

(*
    embed (eval alpha) = alpha:
    For each A and f : [X ->c A],
      embed(alpha_X(id))(A)(f)
        = F(f)(alpha_X(id))
        = alpha_A(f ∘ id)        [naturality of alpha applied at id]
        = alpha_A(f)

    The key step uses the naturality of alpha at f : hom X A, evaluated
    at [id_X]:
      F(f) ∘ alpha_X = alpha_A ∘ repr_mor(f)
    so  F(f)(alpha_X(id)) = alpha_A(repr_mor(f)(id)) = alpha_A(f ∘ id) = alpha_A(f).
*)
Theorem yoneda_embed_eval (alpha : nat_trans (repr_functor X) F) :
    yoneda_embed (yoneda_eval alpha) = alpha.
Proof.
  apply nt_le_antisym;
  intro A; intro f;
  unfold yoneda_eval, yoneda_component; simpl.
  - (* LHS = lcf_mor F X A f (nt_component alpha X (cont_id X)) ⊑ alpha_A f *)
    pose proof (nt_naturality alpha X A f) as nat_eq.
    assert (Hpw : forall z,
      (lcf_mor F X A f ⊚ nt_component alpha X) z =
      (nt_component alpha A ⊚ lcf_mor (repr_functor X) X A f) z).
    { intro z. apply (f_equal (fun (h : [_ →c _]) => h z)). exact nat_eq. }
    simpl in Hpw.
    etransitivity.
    { exact (eq_ind_r (fun v => v ⊑ _) (le_refl _) (Hpw (cont_id X))). }
    simpl. rewrite cont_comp_id_r. exact (le_refl _).
  - pose proof (nt_naturality alpha X A f) as nat_eq.
    assert (Hpw : forall z,
      (lcf_mor F X A f ⊚ nt_component alpha X) z =
      (nt_component alpha A ⊚ lcf_mor (repr_functor X) X A f) z).
    { intro z. apply (f_equal (fun (h : [_ →c _]) => h z)). exact nat_eq. }
    simpl in Hpw.
    etransitivity.
    2: { exact (eq_ind_r (fun v => _ ⊑ v) (le_refl _) (Hpw (cont_id X))). }
    simpl. rewrite cont_comp_id_r. exact (le_refl _).
Qed.


(* ------------------------------------------------------------------ *)
(*   Monotonicity and continuity of the Yoneda maps                    *)
(* ------------------------------------------------------------------ *)
(*
    Since [nat_trans (repr_functor X) F] does not carry HB instances
    (to avoid universe inconsistencies — see NatTrans.v), we state
    monotonicity and continuity using the standalone [nt_le], [nt_chain],
    and [nt_sup] operations rather than [monotone] / [continuous] /
    [cont_fun].
*)

(*
    [yoneda_eval] is monotone: if [alpha <= beta] pointwise,
    then [alpha_X(id) <= beta_X(id)].
*)
Lemma yoneda_eval_mono (alpha beta : nat_trans (repr_functor X) F) :
    nt_le alpha beta -> yoneda_eval alpha ⊑ yoneda_eval beta.
Proof.
  intro Hab. unfold yoneda_eval.
  exact (Hab X (cont_id X)).
Qed.

(*
    Map an [nt_chain] through [yoneda_eval] to get a chain
    in [lcf_obj F X].
*)
Definition yoneda_eval_chain (cs : nt_chain (repr_functor X) F) :
    chain (lcf_obj F X).
Proof.
  unshelve econstructor.
  - exact (fun n => yoneda_eval (ntch cs n)).
  - intros m n Hmn. apply yoneda_eval_mono. exact (ntch_mono cs m n Hmn).
Defined.

(*
    [yoneda_eval] preserves suprema:
      yoneda_eval (nt_sup cs) = sup (yoneda_eval_chain cs)
*)
Lemma yoneda_eval_cont (cs : nt_chain (repr_functor X) F) :
    yoneda_eval (nt_sup cs) = ⊔ (yoneda_eval_chain cs).
Proof.
  unfold yoneda_eval. simpl.
  apply sup_ext. intro n. reflexivity.
Qed.

(*
    [yoneda_embed] is monotone: if [x <= y], then for all A and f,
    [F(f)(x) <= F(f)(y)] by monotonicity of F(f).
*)
Lemma yoneda_embed_mono (x y : lcf_obj F X) :
    x ⊑ y -> nt_le (yoneda_embed x) (yoneda_embed y).
Proof.
  intros Hxy A f. simpl. unfold yoneda_component.
  exact (mf_mono (cf_mono (lcf_mor F X A f)) x y Hxy).
Qed.

(*
    Map a [chain (lcf_obj F X)] through [yoneda_embed] to get
    an [nt_chain].
*)
Definition yoneda_embed_chain (cs : chain (lcf_obj F X)) :
    nt_chain (repr_functor X) F.
Proof.
  unshelve econstructor.
  - exact (fun n => yoneda_embed (cs.[n])).
  - intros m n Hmn. apply yoneda_embed_mono. exact (ch_mono cs m n Hmn).
Defined.

(*
    [yoneda_embed] preserves suprema:
    For a chain [cs : chain (lcf_obj F X)]:
      yoneda_embed (sup cs) = nt_sup (yoneda_embed_chain cs)

    At each A and f:
      lcf_mor F X A f (sup cs) = sup_n (lcf_mor F X A f (cs.[n]))
    because lcf_mor F X A f is a cont_fun (hence Scott-continuous).
*)
Lemma yoneda_embed_cont (cs : chain (lcf_obj F X)) :
    yoneda_embed (⊔ cs) = nt_sup (yoneda_embed_chain cs).
Proof.
  apply nt_le_antisym; intro A; intro f; simpl;
  unfold yoneda_component.
  - (* lcf_mor F X A f (sup cs) ⊑ sup_n (lcf_mor F X A f (cs.[n])) *)
    rewrite (cf_cont (lcf_mor F X A f : [lcf_obj F X →c lcf_obj F A]) cs).
    unfold fun_sup_fun.
    apply sup_least; intro n. simpl.
    exact (sup_upper (pointwise_chain
      (nt_component_chain (yoneda_embed_chain cs) A) f) n).
  - (* sup_n (lcf_mor F X A f (cs.[n])) ⊑ lcf_mor F X A f (sup cs) *)
    apply sup_least; intro n. simpl.
    apply (mf_mono (cf_mono (lcf_mor F X A f : [lcf_obj F X →c lcf_obj F A]))).
    exact (sup_upper cs n).
Qed.


(* ------------------------------------------------------------------ *)
(*   The Yoneda isomorphism as a pair of continuous inverse maps        *)
(* ------------------------------------------------------------------ *)

(*
    The enriched Yoneda lemma: the space of natural transformations
    [nat_trans (repr_functor X) F] is isomorphic to [lcf_obj F X],
    via the pair (yoneda_eval, yoneda_embed) which:
    - are inverse to each other ([yoneda_iso_l], [yoneda_iso_r]);
    - preserve order and suprema of chains
      ([yoneda_eval_mono], [yoneda_eval_cont],
       [yoneda_embed_mono], [yoneda_embed_cont]).
*)

Theorem yoneda_iso_l (x : lcf_obj F X) :
    yoneda_eval (yoneda_embed x) = x.
Proof. exact (yoneda_eval_embed x). Qed.

Theorem yoneda_iso_r (alpha : nat_trans (repr_functor X) F) :
    yoneda_embed (yoneda_eval alpha) = alpha.
Proof. exact (yoneda_embed_eval alpha). Qed.

End YonedaLemma.

Arguments repr_functor X : clear implicits.
Arguments yoneda_eval {X F} alpha.
Arguments yoneda_embed {X} F x.
