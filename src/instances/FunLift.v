(*  FunLift

    Concrete [MixedLCFunctor] instance: the lifted function-space
    bifunctor  [(A, B) ↦ ⟨[A →c B]⟩⊥]  on [CPO.type].

    This registers [CPO.type] as a [MixedLCFunctor], connecting the
    abstract bilimit machinery in [DomainEquations.v] to the concrete
    domain constructors in [FunctionSpaces.v] and [Lift.v].

    Contents:
    - §1  [lift_map]: functorial action of the lift on morphisms
    - §2  [HasMixedEndo] instance: [FL_obj] and [FL_mor]
    - §3  Monotonicity and continuity of [FL_mor]
    - §4  [IsMixedLocallyContinuous] instance: the six axioms

    References:
      Abramsky & Jung (1994) §5.2-5.3
      design-decisions.md DD-005, DD-017
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Theory Require Import
  OrderTheory ChainTheory CPOTheory FunctionSpaces Lift DomainEquations.
From DomainTheory.Instances Require Import Function.


(* ================================================================== *)
(*  §1  lift_map : functorial action of the lift                      *)
(* ================================================================== *)
(*
    [lift_map f] lifts a continuous function [f : [D →c E]] to
    act on the flat lift: [lift_map f : [⟨D⟩⊥ →c ⟨E⟩⊥]].

      lift_map f (Some d) = Some (f d)
      lift_map f None     = None

    Defined as [kleisli (ret ∘ f)].
*)

Section LiftMap.
Context {D E : CPO.type}.

Definition lift_map (f : [D →c E]) : [⟨D⟩⊥ →c ⟨E⟩⊥] :=
  kleisli (cont_comp ret f).

Lemma lift_map_some (f : [D →c E]) (d : D) :
    lift_map f (Some d) = Some (f d).
Proof. reflexivity. Qed.

Lemma lift_map_none (f : [D →c E]) :
    lift_map f None = None.
Proof. reflexivity. Qed.

End LiftMap.

Lemma lift_map_id (D : CPO.type) :
    lift_map (cont_id D) = cont_id ⟨D⟩⊥.
Proof.
  apply cont_fun_ext; intro x.
  destruct x; reflexivity.
Qed.

Lemma lift_map_comp {D E F : CPO.type} (g : [E →c F]) (f : [D →c E]) :
    lift_map (cont_comp g f) = cont_comp (lift_map g) (lift_map f).
Proof.
  apply cont_fun_ext; intro x.
  destruct x; reflexivity.
Qed.

Lemma lift_map_mono {D E : CPO.type} (f1 f2 : [D →c E]) :
    fun_le f1 f2 -> forall x : ⟨D⟩⊥, lift_map f1 x ⊑ lift_map f2 x.
Proof.
  intros Hle x. destruct x; simpl.
  - exact (Hle s).
  - exact I.
Qed.


(* ================================================================== *)
(*  §2  HasMixedEndo instance                                        *)
(* ================================================================== *)
(*
    Object action: [FL_obj A B := ⟨[A →c B]⟩⊥].

    Morphism action: given [f : [A2 →c A1]] (contra) and [g : [B1 →c B2]] (co),

      FL_mor f g : [⟨[A1 →c B1]⟩⊥ →c ⟨[A2 →c B2]⟩⊥]
      FL_mor f g (Some h) = Some (g ∘ h ∘ f)
      FL_mor f g  None    = None

    Built from [lift_map] applied to [cont_postcomp g ∘ cont_precomp f],
    the sandwich [h ↦ g ∘ h ∘ f].
*)

Section FLMorDef.

Definition FL_obj (A B : CPO.type) : CPO.type := ⟨[A →c B]⟩⊥.

Definition FL_sandwich {A1 A2 B1 B2 : CPO.type}
    (f : [A2 →c A1]) (g : [B1 →c B2])
    : [[A1 →c B1] →c [A2 →c B2]] :=
  cont_comp (cont_postcomp g) (cont_precomp f).

Lemma FL_sandwich_apply {A1 A2 B1 B2 : CPO.type}
    (f : [A2 →c A1]) (g : [B1 →c B2]) (h : [A1 →c B1]) :
    FL_sandwich f g h = cont_comp g (cont_comp h f).
Proof. reflexivity. Qed.

Definition FL_mor {A1 A2 B1 B2 : CPO.type}
    (f : hom A2 A1) (g : hom B1 B2)
    : hom (FL_obj A1 B1) (FL_obj A2 B2) :=
  lift_map (FL_sandwich f g).

Lemma FL_mor_some {A1 A2 B1 B2 : CPO.type}
    (f : [A2 →c A1]) (g : [B1 →c B2]) (h : [A1 →c B1]) :
    FL_mor f g (Some h) = Some (cont_comp g (cont_comp h f)).
Proof. reflexivity. Qed.

Lemma FL_mor_none {A1 A2 B1 B2 : CPO.type}
    (f : [A2 →c A1]) (g : [B1 →c B2]) :
    FL_mor f g None = None.
Proof. reflexivity. Qed.

End FLMorDef.


(* ================================================================== *)
(*  §3  Monotonicity and continuity of FL_mor                         *)
(* ================================================================== *)

Section FLMorProperties.

(*
    After [cont_fun_ext; intro x; destruct x], the goal contains
    coercion-wrapped terms that prevent [rewrite FL_mor_some] from
    matching.  We use [change] to convert the goal to the known
    reduced form [Some (g ∘ h ∘ f)] / [None], bypassing the
    coercion chain entirely.
*)

(* --- Identity --- *)

Lemma FL_mor_id (A B : CPO.type) :
    FL_mor (cont_id A) (cont_id B) = cont_id (FL_obj A B).
Proof.
  apply cont_fun_ext; intro x.
  destruct x as [h |].
  - change (Some (cont_comp (cont_id B) (cont_comp h (cont_id A))) = Some h).
    f_equal. rewrite cont_comp_id_l, cont_comp_id_r. reflexivity.
  - reflexivity.
Qed.

(* --- Composition (bifunctoriality) --- *)

Lemma FL_mor_comp {A1 A2 A3 B1 B2 B3 : CPO.type}
    (h : [A2 →c A1]) (f : [A3 →c A2])
    (k : [B1 →c B2]) (g : [B2 →c B3]) :
    cont_comp (FL_mor f g) (FL_mor h k) =
    FL_mor (cont_comp h f) (cont_comp g k).
Proof.
  apply cont_fun_ext; intro x.
  destruct x as [p |].
  - change (Some (cont_comp g (cont_comp (cont_comp k (cont_comp p h)) f)) =
            Some (cont_comp (cont_comp g k) (cont_comp p (cont_comp h f)))).
    f_equal. rewrite !cont_comp_assoc. reflexivity.
  - reflexivity.
Qed.

(* --- Monotonicity in the left (contravariant) argument --- *)

Lemma FL_mor_mono_l {A1 A2 B1 B2 : CPO.type}
    (f f' : [A2 →c A1]) (g : [B1 →c B2]) :
    fun_le f f' -> fun_le (FL_mor f g) (FL_mor f' g).
Proof.
  intros Hf x. destruct x as [h |].
  - change (cont_comp g (cont_comp h f) ⊑ cont_comp g (cont_comp h f')).
    intro d. apply (mf_mono (cf_mono g)). apply (mf_mono (cf_mono h)).
    exact (Hf d).
  - exact I.
Qed.

(* --- Monotonicity in the right (covariant) argument --- *)

Lemma FL_mor_mono_r {A1 A2 B1 B2 : CPO.type}
    (f : [A2 →c A1]) (g g' : [B1 →c B2]) :
    fun_le g g' -> fun_le (FL_mor f g) (FL_mor f g').
Proof.
  intros Hg x. destruct x as [h |].
  - change (cont_comp g (cont_comp h f) ⊑ cont_comp g' (cont_comp h f)).
    intro d. exact (Hg (h (f d))).
  - exact I.
Qed.

(* --- Continuity in the left (contravariant) argument --- *)

Lemma FL_mor_cont_l {A1 A2 B1 B2 : CPO.type} (g : [B1 →c B2]) :
    @continuous
      (hom A2 A1)
      (hom (FL_obj A1 B1) (FL_obj A2 B2))
      (Build_mono_fun
        (fun f => FL_mor f g)
        (fun f f' Hle => FL_mor_mono_l f f' g Hle)).
Proof.
  intro fs.
  set (mono_f := Build_mono_fun
    (fun f => FL_mor f g)
    (fun f f' Hle => FL_mor_mono_l f f' g Hle)).
  apply cont_fun_ext; intro x.
  (* Expand RHS using sup_apply *)
  etransitivity.
  2: { symmetry. exact (sup_apply (map_chain mono_f fs) x). }
  destruct x as [h |].
  - (* Some h: LHS convertible to Some(FL_sandwich (⊔ fs) g h) *)
    set (ghf := cont_comp (@cont_postcomp A2 B1 B2 g)
                           (@cont_postcomp A2 A1 B1 h)).
    assert (Hinner : FL_sandwich (⊔ fs) g h = ⊔ (map_chain (cf_mono ghf) fs)).
    { exact (cf_cont ghf fs). }
    change (Some (FL_sandwich (⊔ fs) g h) =
            (⊔ (map_chain mono_f fs)) (Some h)).
    rewrite Hinner.
    etransitivity.
    { exact (continuous_ret (map_chain (cf_mono ghf) fs)). }
    subst mono_f.
    apply sup_ext; intro n. reflexivity.
  - (* None: both sides reduce to None *)
    assert (Hall : forall n,
      (pointwise_chain (map_chain mono_f fs) None).[n] = None).
    { intro n. subst mono_f. reflexivity. }
    subst mono_f. simpl.
    symmetry. exact (lift_sup_none _ Hall).
Qed.

(* --- Continuity in the right (covariant) argument --- *)

Lemma FL_mor_cont_r {A1 A2 B1 B2 : CPO.type} (f : [A2 →c A1]) :
    @continuous
      (hom B1 B2)
      (hom (FL_obj A1 B1) (FL_obj A2 B2))
      (Build_mono_fun
        (fun g => FL_mor f g)
        (fun g g' Hle => FL_mor_mono_r f g g' Hle)).
Proof.
  intro gs.
  set (mono_g := Build_mono_fun
    (fun g => FL_mor f g)
    (fun g g' Hle => FL_mor_mono_r f g g' Hle)).
  apply cont_fun_ext; intro x.
  etransitivity.
  2: { symmetry. exact (sup_apply (map_chain mono_g gs) x). }
  destruct x as [h |].
  - (* Some h *)
    set (hf := cont_comp h f).
    set (post_hf := @cont_precomp A2 _ B2 hf).
    assert (Hinner : FL_sandwich f (⊔ gs) h = ⊔ (map_chain (cf_mono post_hf) gs)).
    { unfold FL_sandwich. simpl.
      transitivity (cont_comp (⊔ gs) hf).
      { reflexivity. }
      exact (cf_cont post_hf gs). }
    change (Some (FL_sandwich f (⊔ gs) h) =
            (⊔ (map_chain mono_g gs)) (Some h)).
    rewrite Hinner.
    etransitivity.
    { exact (continuous_ret (map_chain (cf_mono post_hf) gs)). }
    subst mono_g.
    apply sup_ext; intro n. reflexivity.
  - (* None: both sides reduce to None *)
    assert (Hall : forall n,
      (pointwise_chain (map_chain mono_g gs) None).[n] = None).
    { intro n. subst mono_g. reflexivity. }
    subst mono_g. simpl.
    symmetry. exact (lift_sup_none _ Hall).
Qed.

End FLMorProperties.


(* ================================================================== *)
(*  §4  HB instances: HasMixedEndo + IsMixedLocallyContinuous         *)
(* ================================================================== *)
(*
    Both HB instances are registered together, AFTER all the property
    lemmas.  This avoids canonical-structure resolution interfering
    with [FL_mor_some] / [FL_mor_none] rewrites during proofs.
*)

HB.instance Definition CPO_HasMixedEndo :=
  HasMixedEndo.Build CPO.type FL_obj
    (fun A1 A2 B1 B2 f g => FL_mor f g).

HB.instance Definition CPO_IsMixedLocallyContinuous :=
  IsMixedLocallyContinuous.Build CPO.type
    FL_mor_id
    (fun A1 A2 A3 B1 B2 B3 h f k g => FL_mor_comp h f k g)
    (fun A1 A2 B1 B2 f f' g Hle => FL_mor_mono_l f f' g Hle)
    (fun A1 A2 B1 B2 f g g' Hle => FL_mor_mono_r f g g' Hle)
    (fun A1 A2 B1 B2 g => FL_mor_cont_l g)
    (fun A1 A2 B1 B2 f => FL_mor_cont_r f).
