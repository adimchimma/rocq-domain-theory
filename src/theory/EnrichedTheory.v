(*  EnrichedTheory

    Phase 1: Derived theory for CPO-enriched categories and locally
    continuous functors.

    Imports:
      [src/structures/Order.v]     — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]       — CPO, continuous
      [src/structures/Morphisms.v] — cont_fun, cont_comp, cont_id
      [src/structures/Enriched.v]  — CPOEnrichedCat, LocallyContinuousFunctor,
                                     comp_l_cont_fun, comp_r_cont_fun, F_mor_cont_fun
      [src/theory/OrderTheory.v]   — le_antisym, chain_mono_le
      [src/theory/ChainTheory.v]   — coherent_family, diag_chain
      [src/theory/CPOTheory.v]     — sup_least, sup_upper, sup_ext,
                                     continuous_of_le, mono_sup_le
      [src/theory/Products.v]      — product CPO, fst_mono, snd_mono,
                                     prod_sup_fst, prod_sup_snd, mono_pair
      [src/theory/FunctionSpaces.v]— fun_le, fun_sup, sup_apply

    Contents
    ========
    §1  Continuity equations
          [comp_cont_l_eq], [comp_cont_r_eq]: equational rewrite forms of
          the separate-continuity axioms from [IsCPOEnriched].
          [F_mor_sup_eq]: F preserves chain sups.

    §2  Joint continuity of composition  (A&J Lemma 3.2.6 / DD-002)
          [comp_joint_mono]: (f, g) ↦ f ⊚ g is monotone on the product CPO.
          [comp_joint_continuous]: jointly Scott-continuous.
          [comp_joint_cont_fun]: packaged as a [cont_fun].
          Proof strategy: double-sup + diagonal collapse.

    §3  Locally continuous functor record
          [lc_functor]: plain record bundling an endofunctor on a
          CPO-enriched category with the locally-continuous axioms.
          [lc_functor_of_hb]: every HB [LocallyContinuousFunctor] yields
          an [lc_functor].
          [lc_functor_mor_eq]: [lcf_mor F] preserves chain sups.
          [id_lc_functor]: the identity endofunctor.
          [comp_lc_functor]: composition of two locally continuous
          endofunctors.

    §4  Embedding-projection pairs
          [ep_pair]: record with embedding [ep_emb], projection [ep_proj],
          retract equation [ep_retract], and deflation inequality
          [ep_deflation].
          [ep_id]: identity ep-pair on any object.
          [ep_comp]: composition of ep-pairs is an ep-pair.
          [ep_emb_mono], [ep_proj_mono]: embeddings and projections are
          monotone functions (preservation of order in the hom-CPO).

    References:
      Abramsky & Jung §5.2 (enriched categories, locally continuous functors)
      Benton-Kennedy §4 (ep-pairs, bilimit construction)
      design-decisions.md §DD-002 (separate vs joint continuity)
      design-decisions.md §DD-004 (Leibniz equality for categorical laws)
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Theory Require Import
  OrderTheory ChainTheory CPOTheory Products FunctionSpaces.

From Stdlib Require Import PeanoNat.


(* ================================================================== *)
(*   §1  Continuity equations                                          *)
(* ================================================================== *)
(*
    The axioms [comp_cont_l] and [comp_cont_r] in [IsCPOEnriched] are
    stated as [continuous] witnesses.  The lemmas below recast them as
    explicit equations suitable for [rewrite].

      [comp_cont_l_eq f c]:   f ⊚ (⊔ c) = ⊔ (map_chain (comp_l_cont_fun f) c)
      [comp_cont_r_eq g c]:   (⊔ c) ⊚ g = ⊔ (map_chain (comp_r_cont_fun g) c)
      [F_mor_sup_eq c]:       F_mor (⊔ c) = ⊔ (map_chain F_mor_cont_fun c)

    These are just the [cf_cont] field of the packaged cont_fun definitions
    from [Enriched.v], restated for clarity.
*)

Section ContEqLemmas.
Context {C : CPOEnrichedCat.type} {A B D : C}.

(*
    [comp_cont_l_eq]: post-composition with [f] commutes with chain sups.
    [comp_l_cont_fun f] is the cont_fun [g ↦ f ⊚ g] from [Enriched.v].
*)
Lemma comp_cont_l_eq (f : hom B D) (c : chain (hom A B)) :
    f ⊚ (⊔ c) = ⊔ (map_chain (cf_mono (comp_l_cont_fun f)) c).
Proof.
  exact (cf_cont (comp_l_cont_fun f) c).
Qed.

(*
    [comp_cont_r_eq]: pre-composition with [g] commutes with chain sups.
    [comp_r_cont_fun g] is the cont_fun [f ↦ f ⊚ g] from [Enriched.v].
*)
Lemma comp_cont_r_eq (g : hom A B) (c : chain (hom B D)) :
    (⊔ c) ⊚ g = ⊔ (map_chain (cf_mono (comp_r_cont_fun g)) c).
Proof.
  exact (cf_cont (comp_r_cont_fun g) c).
Qed.

End ContEqLemmas.


Section FMorSup.
Context {C : LocallyContinuousFunctor.type} {A B : C}.

(*
    [F_mor_sup_eq]: a locally continuous functor preserves chain sups in
    each hom-CPO.
    [F_mor_cont_fun] is the cont_fun [h ↦ F_mor h] from [Enriched.v].
*)
Lemma F_mor_sup_eq (c : chain (hom A B)) :
    F_mor A B (⊔ c) = ⊔ (map_chain (cf_mono F_mor_cont_fun) c).
Proof.
  exact (cf_cont F_mor_cont_fun c).
Qed.

End FMorSup.


(* ================================================================== *)
(*   §2  Joint continuity of composition                              *)
(* ================================================================== *)
(*
    Theorem (A&J Lemma 3.2.6, DD-002):
    In any CPO-enriched category, composition is jointly Scott-continuous.

    The proof works in two stages:

    Stage A — product-free formulation:
      Given chains [gs : chain (hom B D)] and [fs : chain (hom A B)],
      define the _diagonal chain_ [comp_chain gs fs] whose n-th element
      is [gs.[n] ⊚ fs.[n]].  The core identity is
        [comp_joint_sup]:  (⊔ gs) ⊚ (⊔ fs) = ⊔ (comp_chain gs fs).
      The proof uses the §1 rewrite lemmas [comp_cont_r_eq] / [comp_cont_l_eq]
      for double-sup elimination, followed by a diagonal collapse via
      [comp_diagonal_bound].

    Stage B — product CPO packaging:
      [comp_joint_mono]: monotone map on [hom A B × hom B D].
      [comp_joint_continuous]: derived from [comp_joint_sup].
      [comp_joint_cont_fun]: packaged as a [cont_fun].

    Note: the proof uses [etransitivity] instead of [le_trans with ...]
    to avoid HB canonical-structure resolution issues on intermediate terms.
*)


(* ------------------------------------------------------------------ *)
(*   Stage A: product-free diagonal chain formulation                 *)
(* ------------------------------------------------------------------ *)

Section CompJointSup.
Context {C : CPOEnrichedCat.type} {A B D : C}.

(*
    The diagonal composition function: [gs.[n] ⊚ fs.[n]].
*)
Definition comp_chain_fun (gs : chain (hom B D)) (fs : chain (hom A B))
    (n : nat) : hom A D :=
  gs.[n] ⊚ fs.[n].

Lemma comp_chain_mono (gs : chain (hom B D)) (fs : chain (hom A B)) :
    forall m n, m <= n -> comp_chain_fun gs fs m ⊑ comp_chain_fun gs fs n.
Proof.
  intros m n Hmn. unfold comp_chain_fun.
  etransitivity.
  - apply comp_mono_r. exact (ch_mono gs m n Hmn).
  - apply comp_mono_l. exact (ch_mono fs m n Hmn).
Qed.

Definition comp_chain (gs : chain (hom B D)) (fs : chain (hom A B))
    : chain (hom A D) :=
  Build_chain (comp_chain_fun gs fs) (comp_chain_mono gs fs).

(*
    Diagonal bound: for any n, m we have
      gs.[n] ⊚ fs.[m] ⊑ ⊔ (comp_chain gs fs)
    via k = max(n, m).
*)
Lemma comp_diagonal_bound (gs : chain (hom B D)) (fs : chain (hom A B))
    (n m : nat) :
    gs.[n] ⊚ fs.[m] ⊑ ⊔ (comp_chain gs fs).
Proof.
  set (k := Nat.max n m).
  etransitivity.
  - etransitivity.
    + apply comp_mono_r. exact (ch_mono gs n k (Nat.le_max_l n m)).
    + apply comp_mono_l. exact (ch_mono fs m k (Nat.le_max_r n m)).
  - exact (sup_upper (comp_chain gs fs) k).
Qed.

(*
    Core identity: (⊔ gs) ⊚ (⊔ fs) = ⊔ (comp_chain gs fs).
    ≤ direction: double-sup elimination using [comp_cont_r_eq] then
      [comp_cont_l_eq], followed by diagonal collapse.
    ≥ direction: each diagonal element is below the double composition.
*)
Theorem comp_joint_sup (gs : chain (hom B D)) (fs : chain (hom A B)) :
    (⊔ gs) ⊚ (⊔ fs) = ⊔ (comp_chain gs fs).
Proof.
  apply le_antisym.
  - rewrite (comp_cont_r_eq (⊔ fs) gs).
    apply sup_least. intro n.
    change (gs.[n] ⊚ (⊔ fs) ⊑ ⊔ (comp_chain gs fs)).
    rewrite (comp_cont_l_eq (gs.[n]) fs).
    apply sup_least. intro m.
    change (gs.[n] ⊚ fs.[m] ⊑ ⊔ (comp_chain gs fs)).
    exact (comp_diagonal_bound gs fs n m).
  - apply sup_least. intro k.
    change (gs.[k] ⊚ fs.[k] ⊑ (⊔ gs) ⊚ (⊔ fs)).
    etransitivity.
    + apply comp_mono_l. exact (sup_upper fs k).
    + apply comp_mono_r. exact (sup_upper gs k).
Qed.

End CompJointSup.


(* ------------------------------------------------------------------ *)
(*   Stage B: product CPO packaging                                   *)
(* ------------------------------------------------------------------ *)

Section CompJointProduct.
Context {C : CPOEnrichedCat.type} {A B D : C}.

(*
    The joint composition function on the product hom-CPO.
    Defined separately to let Coq resolve HB coercions between
    CPO.sort and the enriched-category carrier.
*)
Definition comp_joint_fun (fg : (hom A B * hom B D)%type) : hom A D :=
  let g := fst fg in
  let f := snd fg in
  f ⊚ g.

Lemma comp_joint_fun_mono :
    monotone (hom A B * hom B D)%type (hom A D) comp_joint_fun.
Proof.
  intros fg1 fg2 H. unfold comp_joint_fun.
  etransitivity.
  - apply comp_mono_l. exact (proj1 H).
  - apply comp_mono_r. exact (proj2 H).
Qed.

Definition comp_joint_mono :
    mono_fun (hom A B * hom B D)%type (hom A D) :=
  Build_mono_fun comp_joint_fun comp_joint_fun_mono.

(*
    Joint continuity derived from [comp_joint_sup].
    The product sup splits as [(⊔ fs, ⊔ gs)] definitionally, so the
    goal reduces to [comp_joint_sup] applied to the projected chains.
*)
Theorem comp_joint_continuous : continuous comp_joint_mono.
Proof.
  apply continuous_of_le. intro c.
  set (fs := map_chain fst_mono c).
  set (gs := map_chain snd_mono c).
  change ((⊔ gs) ⊚ (⊔ fs) ⊑ ⊔ (map_chain comp_joint_mono c)).
  rewrite (comp_joint_sup gs fs).
  apply sup_least. intro k.
  change (gs.[k] ⊚ fs.[k] ⊑ ⊔ (map_chain comp_joint_mono c)).
  exact (sup_upper (map_chain comp_joint_mono c) k).
Qed.

Definition comp_joint_cont_fun :
    [(hom A B * hom B D)%type →c (hom A D)] :=
  Build_cont_fun comp_joint_mono comp_joint_continuous.

Lemma comp_joint_apply (fg : (hom A B * hom B D)%type) :
    comp_joint_cont_fun fg = (snd fg) ⊚ (fst fg).
Proof. reflexivity. Qed.

End CompJointProduct.


(* ================================================================== *)
(*   §3  Locally continuous functor record                            *)
(* ================================================================== *)
(*
    [lc_functor C] bundles the data and axioms of a locally continuous
    endofunctor on [C].  This is the "plain" (non-HB) counterpart to the
    [LocallyContinuousFunctor] HB structure, and allows working with
    multiple endofunctors on the same base category in a single context.

    This record mirrors [IsLocallyContinuous] (from [Enriched.v]) with the
    same fields, but without the HB universe machinery.  Every HB
    [LocallyContinuousFunctor] gives an [lc_functor] via [lc_functor_of_hb].
*)

Record lc_functor (C : CPOEnrichedCat.type) := {
  lcf_obj  : C -> C;
  lcf_mor  : forall (A B : C), hom A B -> hom (lcf_obj A) (lcf_obj B);
  lcf_mono : forall (A B : C),
      monotone (hom A B) (hom (lcf_obj A) (lcf_obj B)) (lcf_mor A B);
  lcf_cont : forall (A B : C),
      @continuous (hom A B) (hom (lcf_obj A) (lcf_obj B))
        (Build_mono_fun (lcf_mor A B) (lcf_mono A B));
  lcf_id   : forall (A : C),
      lcf_mor A A (id_mor A) = id_mor (lcf_obj A);
  lcf_comp : forall (A B D : C) (f : hom B D) (g : hom A B),
      lcf_mor A D (f ⊚ g) = (lcf_mor B D f) ⊚ (lcf_mor A B g);
}.

Arguments lcf_obj  {C}.
Arguments lcf_mor  {C}.
Arguments lcf_mono {C}.
Arguments lcf_cont {C}.
Arguments lcf_id   {C}.
Arguments lcf_comp {C}.


(* Accessors: packaged mono_fun and cont_fun for [lcf_mor]. *)

Definition lcf_mono_fun {C : CPOEnrichedCat.type} (F : lc_functor C)
    {A B : C} : mono_fun (hom A B) (hom (lcf_obj F A) (lcf_obj F B)) :=
  Build_mono_fun (lcf_mor F A B) (lcf_mono F A B).

Definition lcf_cont_fun {C : CPOEnrichedCat.type} (F : lc_functor C)
    {A B : C} : [(hom A B) →c (hom (lcf_obj F A) (lcf_obj F B))] :=
  Build_cont_fun (lcf_mono_fun F) (lcf_cont F A B).


(*
    Every [LocallyContinuousFunctor.type] instance carries an [lc_functor].
    This allows using the [lc_functor] record API with HB-registered functors.
*)
Definition lc_functor_of_hb (C : LocallyContinuousFunctor.type) :
    lc_functor C.
Proof.
  unshelve econstructor.
  - (* lcf_obj *)  exact (fun A => F_obj A).
  - (* lcf_mor *)  exact (fun A B h => F_mor A B h).
  - (* lcf_mono *) intros A B. exact (@F_mor_mono C A B).
  - (* lcf_cont *) intros A B. exact (@F_mor_cont C A B).
  - (* lcf_id *)   intro A. exact (F_mor_id A).
  - (* lcf_comp *) intros A B D f g. exact (@F_mor_comp C A B D f g).
Defined.

(*
    [lc_functor_mor_eq]: a locally continuous functor preserves chain sups.
    This is the [lc_functor] version of [F_mor_sup_eq] (§1).
*)
Lemma lc_functor_mor_eq {C : CPOEnrichedCat.type} (F : lc_functor C)
    {A B : C} (c : chain (hom A B)) :
    lcf_mor F A B (⊔ c) = ⊔ (map_chain (lcf_mono_fun F) c).
Proof.
  exact (cf_cont (lcf_cont_fun F) c).
Qed.


(* ------------------------------------------------------------------ *)
(*   Identity locally continuous functor                              *)
(* ------------------------------------------------------------------ *)
(*
    The identity endofunctor [id_lc_functor C] on any CPO-enriched
    category [C]:
      lcf_obj  := fun A => A
      lcf_mor  := fun A B f => f

    All axioms reduce to [reflexivity].
*)

Definition id_lc_functor (C : CPOEnrichedCat.type) : lc_functor C.
Proof.
  refine {|
    lcf_obj  := fun A => A;
    lcf_mor  := fun A B f => f;
    lcf_mono := fun A B f1 f2 Hle => Hle;
    lcf_cont := _;
    lcf_id   := fun A => eq_refl;
    lcf_comp := fun A B D f g => eq_refl;
  |}.
  (*
      Continuity of the identity: [id (⊔ c) = ⊔ (map_chain id c)].
      The [map_chain] of the identity mono_fun is pointwise equal to [c],
      so both sups agree.
  *)
  intros A B c.
  apply sup_ext; intro n.
  reflexivity.
Defined.

Lemma id_lcf_obj {C : CPOEnrichedCat.type} (A : C) :
    lcf_obj (id_lc_functor C) A = A.
Proof. reflexivity. Qed.

Lemma id_lcf_mor {C : CPOEnrichedCat.type} {A B : C} (f : hom A B) :
    lcf_mor (id_lc_functor C) A B f = f.
Proof. reflexivity. Qed.


(* ------------------------------------------------------------------ *)
(*   Composition of locally continuous functors                       *)
(* ------------------------------------------------------------------ *)
(*
    Given two locally continuous endofunctors [F] and [G] on [C], their
    composite [comp_lc_functor G F] is the endofunctor
      lcf_obj  := G.obj ∘ F.obj
      lcf_mor  := G.mor ∘ F.mor

    Continuity: [G.mor (F.mor (⊔ c))] unfolds to [G.mor (⊔ (F.mor ∘ c))]
    by continuity of [F], then to [⊔ (G.mor ∘ F.mor ∘ c)] by continuity of [G].
    The [map_chain] of the composite is [map_chain (G.mor ∘ F.mor)].
*)

Definition comp_lc_functor {C : CPOEnrichedCat.type}
    (G F : lc_functor C) : lc_functor C.
Proof.
  unshelve econstructor.
  - (* lcf_obj *) exact (fun A => lcf_obj G (lcf_obj F A)).
  - (* lcf_mor *) exact (fun A B h =>
      lcf_mor G (lcf_obj F A) (lcf_obj F B) (lcf_mor F A B h)).
  - (*  Monotonicity: G_mono (F_mono Hle).  *)
    intros A B f1 f2 Hle.
    apply (lcf_mono G).
    apply (lcf_mono F).
    exact Hle.
  - (*  Continuity: G(F(⊔ c)) = G(⊔ F(c)) = ⊔ G(F(c)). *)
    intros A B c. cbn [mf_fun].
    rewrite (lc_functor_mor_eq F c).
    rewrite (lc_functor_mor_eq G (map_chain (lcf_mono_fun F) c)).
    apply sup_ext; intro n.
    reflexivity.
  - (*  Identity: G(F(id)) = G(id) = id.  *)
    intro A. cbv beta.
    rewrite (lcf_id F A).
    exact (lcf_id G (lcf_obj F A)).
  - (*  Composition: G(F(f ⊚ g)) = G(F f ⊚ F g) = G(F f) ⊚ G(F g).  *)
    intros A B D0 f g. cbv beta.
    rewrite (lcf_comp F A B D0 f g).
    exact (lcf_comp G (lcf_obj F A) (lcf_obj F B) (lcf_obj F D0) _ _).
Defined.

Lemma comp_lcf_obj {C : CPOEnrichedCat.type} (G F : lc_functor C) (A : C) :
    lcf_obj (comp_lc_functor G F) A = lcf_obj G (lcf_obj F A).
Proof. reflexivity. Qed.

Lemma comp_lcf_mor {C : CPOEnrichedCat.type} (G F : lc_functor C)
    {A B : C} (f : hom A B) :
    lcf_mor (comp_lc_functor G F) A B f =
      lcf_mor G (lcf_obj F A) (lcf_obj F B) (lcf_mor F A B f).
Proof. reflexivity. Qed.

(*
    Associativity and identity laws for lc_functor composition.
    These hold pointwise on the object and morphism functions.
*)

Lemma comp_lcf_assoc {C : CPOEnrichedCat.type} (H G F : lc_functor C)
    {A B : C} (f : hom A B) :
    lcf_mor (comp_lc_functor H (comp_lc_functor G F)) A B f =
    lcf_mor (comp_lc_functor (comp_lc_functor H G) F) A B f.
Proof. reflexivity. Qed.

Lemma comp_lcf_id_l {C : CPOEnrichedCat.type} (F : lc_functor C)
    {A B : C} (f : hom A B) :
    lcf_mor (comp_lc_functor (id_lc_functor C) F) A B f =
    lcf_mor F A B f.
Proof. reflexivity. Qed.

Lemma comp_lcf_id_r {C : CPOEnrichedCat.type} (F : lc_functor C)
    {A B : C} (f : hom A B) :
    lcf_mor (comp_lc_functor F (id_lc_functor C)) A B f =
    lcf_mor F A B f.
Proof. reflexivity. Qed.


(* ================================================================== *)
(*   §4  Embedding-projection pairs                                   *)
(* ================================================================== *)
(*
    An _embedding-projection pair_ (ep-pair) between objects [A] and [B]
    in a CPO-enriched category consists of:

      ep_emb  : hom A B   — the embedding (a section)
      ep_proj : hom B A   — the projection (a retraction)

    satisfying:

      ep_retract   : p ⊚ e = id_mor A      — [p] is a left inverse of [e]
      ep_deflation : e ⊚ p ⊑ id_mor B      — [e ⊚ p] is a deflation

    The deflation inequality lives in the hom-CPO [hom B B], where [⊑] is
    the Scott order inherited from the CPO structure.

    This is the standard notion from Abramsky & Jung §5.3 and
    Benton-Kennedy §4; it is the key relation used in the inverse-limit
    (bilimit) construction in [DomainEquations.v].
*)

Record ep_pair {C : CPOEnrichedCat.type} (A B : C) := {
  ep_emb      : hom A B;
  ep_proj     : hom B A;
  ep_retract  : ep_proj ⊚ ep_emb = id_mor A;
  ep_deflation : ep_emb ⊚ ep_proj ⊑ id_mor B;
}.

Arguments ep_emb      {C A B}.
Arguments ep_proj     {C A B}.
Arguments ep_retract  {C A B}.
Arguments ep_deflation {C A B}.

(* ------------------------------------------------------------------ *)
(*   Identity ep-pair                                                  *)
(* ------------------------------------------------------------------ *)

Definition ep_id {C : CPOEnrichedCat.type} (A : C) : ep_pair A A.
Proof.
  unshelve econstructor.
  - exact (id_mor A).
  - exact (id_mor A).
  - exact (@comp_id_l C A A (id_mor A)).
  - (* ep_deflation: id ⊚ id ⊑ id *)
    exact (eq_rect _ (fun x => x ⊑ id_mor A) (le_refl _) _
      (eq_sym (@comp_id_l C A A (id_mor A)))).
Defined.

Lemma ep_id_deflation_eq {C : CPOEnrichedCat.type} (A : C) :
    (ep_emb (ep_id A)) ⊚ (ep_proj (ep_id A)) = id_mor A.
Proof.
  cbv [ep_id ep_emb ep_proj].
  exact (@comp_id_l C A A (id_mor A)).
Qed.


(* ------------------------------------------------------------------ *)
(*   Composition of ep-pairs                                          *)
(* ------------------------------------------------------------------ *)
(*
    Given ep-pairs [ep1 : ep_pair A B] and [ep2 : ep_pair B D], their
    composite is an ep-pair [ep_comp ep2 ep1 : ep_pair A D]:

      emb  := ep2.emb ⊚ ep1.emb
      proj := ep1.proj ⊚ ep2.proj
*)

Definition ep_comp {C : CPOEnrichedCat.type} {A B D : C}
    (ep2 : ep_pair B D) (ep1 : ep_pair A B) : ep_pair A D.
Proof.
  unshelve econstructor.
  - (* ep_emb *)  exact (ep_emb ep2 ⊚ ep_emb ep1).
  - (* ep_proj *) exact (ep_proj ep1 ⊚ ep_proj ep2).
  - (* retract: (p1 ⊚ p2) ⊚ (e2 ⊚ e1) = id *)
    rewrite (@comp_assoc C).
    rewrite <- (@comp_assoc C _ _ _ _ (ep_proj ep2) (ep_emb ep2) (ep_emb ep1)).
    rewrite (ep_retract ep2).
    rewrite (@comp_id_l C).
    exact (ep_retract ep1).
  - (* deflation: (e2 ⊚ e1) ⊚ (p1 ⊚ p2) ⊑ id *)
    rewrite (@comp_assoc C).
    rewrite <- (@comp_assoc C _ _ _ _ (ep_emb ep1) (ep_proj ep1) (ep_proj ep2)).
    etransitivity.
    + apply comp_mono_l.
      apply comp_mono_r.
      exact (ep_deflation ep1).
    + rewrite (@comp_id_l C).
      exact (ep_deflation ep2).
Defined.

Lemma ep_comp_emb {C : CPOEnrichedCat.type} {A B D : C}
    (ep2 : ep_pair B D) (ep1 : ep_pair A B) :
    ep_emb (ep_comp ep2 ep1) = ep_emb ep2 ⊚ ep_emb ep1.
Proof. reflexivity. Qed.

Lemma ep_comp_proj {C : CPOEnrichedCat.type} {A B D : C}
    (ep2 : ep_pair B D) (ep1 : ep_pair A B) :
    ep_proj (ep_comp ep2 ep1) = ep_proj ep1 ⊚ ep_proj ep2.
Proof. reflexivity. Qed.


(* ------------------------------------------------------------------ *)
(*   Basic properties of ep-pairs                                     *)
(* ------------------------------------------------------------------ *)

Section EPairProperties.
Context {C : CPOEnrichedCat.type} {A B : C}.
Variable (ep : ep_pair A B).

Lemma ep_proj_emb_retract :
    ep_proj ep ⊚ ep_emb ep = id_mor A.
Proof.
  exact (ep_retract ep).
Qed.

(*
    The deflation [ep_emb ⊚ ep_proj] composed with [ep_emb]
    on the right gives back [ep_emb] (by the retract equation).
*)
Lemma ep_deflation_emb :
    ep_emb ep ⊚ ep_proj ep ⊚ ep_emb ep = ep_emb ep.
Proof.
  rewrite (@comp_assoc C).
  rewrite (ep_retract ep).
  exact (@comp_id_r C _ _ (ep_emb ep)).
Qed.

(*
    The deflation [ep_emb ⊚ ep_proj] is idempotent.
*)
Lemma ep_deflation_idempotent :
    (ep_emb ep ⊚ ep_proj ep) ⊚ (ep_emb ep ⊚ ep_proj ep) =
    ep_emb ep ⊚ ep_proj ep.
Proof.
  rewrite (@comp_assoc C).
  rewrite <- (@comp_assoc C _ _ _ _ (ep_proj ep) (ep_emb ep) (ep_proj ep)).
  rewrite (ep_retract ep).
  rewrite (@comp_id_l C).
  reflexivity.
Qed.

End EPairProperties.


(* ------------------------------------------------------------------ *)
(*   ep-pairs and the hom-CPO order                                   *)
(* ------------------------------------------------------------------ *)

Section EPOrderLemmas.
Context {C : CPOEnrichedCat.type} {A B : C}.
Variable (ep : ep_pair A B).

(*
    [ep_emb ⊚ ep_proj ⊚ f ⊑ f] for any [f : hom A B],
    from the deflation [ep_emb ⊚ ep_proj ⊑ id].
*)
Lemma ep_deflation_precomp (f : hom A B) :
    ep_emb ep ⊚ ep_proj ep ⊚ f ⊑ f.
Proof.
  etransitivity.
  - apply comp_mono_r.
    exact (ep_deflation ep).
  - rewrite (@comp_id_l C).
    exact (@le_refl (hom A B) f).
Qed.

(*
    The retract ensures that [ep_proj ⊚ ep_emb ⊚ g = g].
*)
Lemma ep_proj_emb_cancel (g : hom B A) :
    ep_proj ep ⊚ ep_emb ep ⊚ g = g.
Proof.
  rewrite (ep_retract ep).
  exact (@comp_id_l C _ _ g).
Qed.

(*
    [ep_emb ⊚ ep_proj ⊚ h ⊑ h] for any [h : hom D B],
    from the deflation [ep_emb ⊚ ep_proj ⊑ id].
*)
Lemma ep_deflation_postcomp (D0 : C) (h : hom D0 B) :
    ep_emb ep ⊚ ep_proj ep ⊚ h ⊑ h.
Proof.
  etransitivity.
  - apply comp_mono_r.
    exact (ep_deflation ep).
  - rewrite (@comp_id_l C).
    exact (@le_refl (hom D0 B) h).
Qed.

End EPOrderLemmas.


(* ------------------------------------------------------------------ *)
(*   Chains of ep-pairs                                               *)
(* ------------------------------------------------------------------ *)
(*
    The bilimit construction in [DomainEquations.v] requires working with
    ω-chains of ep-pairs: sequences
      A_0 ↪ A_1 ↪ A_2 ↪ ...
    where each [ep_i : ep_pair A_i A_{i+1}].
*)

Record ep_chain (C : CPOEnrichedCat.type) := {
  epc_obj  : nat -> C;
  epc_pair : forall n : nat, ep_pair (epc_obj n) (epc_obj (S n));
}.

Arguments epc_obj  {C}.
Arguments epc_pair {C}.

Definition epc_emb {C : CPOEnrichedCat.type} (ec : ep_chain C) (n : nat) :
    hom (epc_obj ec n) (epc_obj ec (S n)) :=
  ep_emb (epc_pair ec n).

Definition epc_proj {C : CPOEnrichedCat.type} (ec : ep_chain C) (n : nat) :
    hom (epc_obj ec (S n)) (epc_obj ec n) :=
  ep_proj (epc_pair ec n).

Lemma epc_retract {C : CPOEnrichedCat.type} (ec : ep_chain C) (n : nat) :
    epc_proj ec n ⊚ epc_emb ec n = id_mor (epc_obj ec n).
Proof.
  exact (ep_retract (epc_pair ec n)).
Qed.

Lemma epc_deflation {C : CPOEnrichedCat.type} (ec : ep_chain C) (n : nat) :
    epc_emb ec n ⊚ epc_proj ec n ⊑ id_mor (epc_obj ec (S n)).
Proof.
  exact (ep_deflation (epc_pair ec n)).
Qed.
