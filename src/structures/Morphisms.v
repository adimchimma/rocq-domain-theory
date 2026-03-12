(** * Morphisms

    Phase 0: Structure-preserving maps.

    Definitions to be added:
    - [IsMonotone]: a map [f : D -> E] that preserves the order.
    - [IsContinuous]: a monotone map that also preserves lubs of omega-chains.
    - Bundled record types [MonoFun] and [ContFun].
    - Identity and composition lemmas.
*)

(** * Morphism Structures

    Monotone and Scott-continuous functions between CPOs, packaged as
    records with categorical structure (identity and composition).

    This is [src/structures/Morphisms.v].  Structure _declarations_ and
    the categorical laws for morphisms live here.  More involved theorems
    (Scott induction, admissibility, the universal property of [cont_fun]
    as an exponential) belong in [src/theory/CPOTheory.v].

    Imports:
      [src/structures/Order.v] — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]   — CPO, PointedCPO, continuous

    Phase coverage:
      Phase 0 — cont_fun, cont_id, cont_comp, strict_fun

    Note on HB migration status:
      [FunctionSpaces.v] already registers [[D →c E]] as a [CPO.type]
      (and [PointedCPO.type]) under the pointwise order via HB instances,
      without converting [cont_fun] itself into an HB structure.

      A full migration — making [mono_fun] and [cont_fun] HB structures
      with [Funclass] keys (i.e. [HB.mixin Record IsMonotone (P Q : Preorder.type)
      (f : P -> Q)]) — would touch 50+ construction sites across ~12 files,
      break proofs that [destruct] these records, and risk fragile
      canonical-structure inference with dependent types (chains, sups).
      The practical benefit (automatic monotonicity/continuity inference
      for composed functions) is small because compositions are already
      handled explicitly via [cont_comp], [cont_id], etc.

      Revisit if: (a) the enriched-hom setting (Phase 2) needs
      [IsMonotone]/[IsContinuous] as composable mixins on the same
      function, or (b) a broader restructuring makes the churn worthwhile.
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO.

From Stdlib Require Import Logic.ProofIrrelevance.

(* ------------------------------------------------------------------ *)
(*   Continuous functions                                             *)
(* ------------------------------------------------------------------ *)
(*
    A Scott-continuous function between CPOs is a monotone function that
    additionally preserves suprema of ω-chains.  The [continuous]
    predicate is already declared in [CPO.v]; here we bundle it with
    the underlying monotone function into a [cont_fun] record.

    The coercion [:>] on [cf_mono] lets a [[D →c E]] be used
    directly as a [mono_fun D E], which in turn coerces to [D -> E]
    via [mf_fun].  So a [cont_fun] can appear anywhere a plain function
    is expected. 
*)
Record cont_fun (D E : CPO.type) : Type := Build_cont_fun {
    cf_mono :> mono_fun D E;
    cf_cont : continuous cf_mono;
}.

Arguments Build_cont_fun {D E} cf_mono cf_cont.
Arguments cf_mono {D E} f : rename.
Arguments cf_cont {D E} f : rename.

(* Notation for the type of Scott-continuous functions.
   [D →c E] is sugar for [cont_fun D E], available to any
   file that imports Morphisms.
   The first argument has no explicit level (i.e., constr) to
   share a compatible prefix with stdlib list notations
   [[ _ ]] and [[ _ ; _ ; .. ; _ ]]. *)
Notation "[ D →c E ]" := (cont_fun D E)
  (at level 0, E at level 200, no associativity).

(*
    Applying a continuous function to a chain still gives a chain
    (inherited from [map_chain] on the underlying [mono_fun]). 
*)
Definition map_chain_cont {D E : CPO.type} (f : [D →c E]) (c : chain D)
   : chain E := map_chain (cf_mono f) c.


(* ------------------------------------------------------------------ *)
(*   Identity and composition                                         *)
(* ------------------------------------------------------------------ *)
(*  
    The identity function is continuous.
    Proof: [id (⊔ c) = ⊔ c = ⊔ (map_chain id c)] because
    [map_chain id c] has the same underlying sequence as [c]. 
*)
Lemma continuous_id {D : CPO.type} : continuous (mono_id D).
Proof.
    intros c.
    apply sup_ext.
    intros n.
    reflexivity.
Qed.

Definition cont_id (D : CPO.type) : [D →c D] :=
    Build_cont_fun (mono_id D) continuous_id.

(* 
    Composition of continuous functions is continuous.
    Proof: [g (f (⊔ c)) = g (⊔ (map_chain f c)) = ⊔ (map_chain g (map_chain f c))]
    using continuity of [f] then [g], and the fact that
    [map_chain g ∘ map_chain f = map_chain (g ∘ f)]. 
*)
Lemma continuous_comp {D E F : CPO.type} (g : [E →c F]) (f : [D →c E]):
    continuous (mono_comp (cf_mono g) (cf_mono f)).
Proof.
    intro c.
    simpl.
    repeat rewrite cf_cont.
    reflexivity.
Qed.

Definition cont_comp {D E F: CPO.type}
    (g : [E →c F]) (f : [D →c E]) : [D →c F] :=
        Build_cont_fun 
                (mono_comp (cf_mono g) (cf_mono f)) 
                (continuous_comp g f).
Notation "g ∘ f" := (cont_comp g f) (at level 40, left associativity).

(*  
    Categorical laws

    These follow immediately from the corresponding laws for [mono_fun]
    since [cont_fun] coerces to [mono_fun] and the proofs are on the
    underlying functions. 
*)
Lemma cont_comp_assoc {D E F G : CPO.type}
    (h : [F →c G]) (g : [E →c F]) (f : [D →c E]) :
        h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
    unfold cont_comp.
    f_equal.
    destruct h, g, f.
    apply proof_irrelevance.
Qed.

Lemma cont_fun_eq {D E : CPO.type} (f g : [D →c E]) :
    cf_mono f = cf_mono g -> f = g.
Proof.
    destruct f as [m1 h1], g as [m2 h2].
    simpl.
    intros H.
    destruct H.
    f_equal.
    apply proof_irrelevance.
Qed.

Lemma cont_comp_id_l {D E : CPO.type} (f : [D →c E]) :
    cont_id E ∘ f = f.
Proof.
    apply cont_fun_eq.
    simpl.
    apply mono_comp_id_l.
Qed.

Lemma cont_comp_id_r {D E : CPO.type} (f : [D →c E]) :
    f ∘ (cont_id D) = f.
Proof.
    apply cont_fun_eq.
    simpl.
    apply mono_comp_id_r.
Qed.


(* ------------------------------------------------------------------ *)
(*   Strict functions (Phase 0, PointedCPO)                           *)
(* ------------------------------------------------------------------ *)
(*  
    A continuous function between pointed CPOs is _strict_ if it
    preserves the least element: [f ⊥ = ⊥].

    Strictness is important for the denotational semantics of
    call-by-value languages and for the lifting monad (Phase 0),
    and will appear again in the PCF semantics (Phase 1). 
*)
Definition strict {D E : PointedCPO.type} (f : [D →c E]) :=
    f ⊥ = ⊥.

Record strict_fun (D E : PointedCPO.type) : Type := Build_strict_fun {
    sf_cont :> [D →c E];
    sf_strict : strict sf_cont;
}.

Arguments Build_strict_fun {D E} sf_cont sf_strict.
Arguments sf_cont {D E} f : rename.
Arguments sf_strict {D E} f : rename.

(* Identity is strict *)
Lemma strict_id {D : PointedCPO.type} : strict (cont_id D).
Proof.
    reflexivity.
Qed.

Definition strict_id_fun (D : PointedCPO.type) : strict_fun D D :=
    Build_strict_fun (cont_id D) strict_id.

(* Composition of strict functions is strict *)
Lemma strict_comp_strict {D E F : PointedCPO.type}
    (g : strict_fun E F) (f : strict_fun D E) :
    strict (cont_comp (sf_cont g) (sf_cont f)).
Proof.
    unfold strict.
    simpl.
    rewrite (sf_strict f).
    exact (sf_strict g).
Qed.

Definition strict_comp {D E F : PointedCPO.type}
    (g : strict_fun E F) (f : strict_fun D E) : strict_fun D F :=
        Build_strict_fun 
            (cont_comp (sf_cont g) (sf_cont f)) (strict_comp_strict g f).