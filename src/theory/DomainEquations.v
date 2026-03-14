(* DomainEquations

    Mixed-variance locally continuous bifunctors and the inverse-limit
    (bilimit) construction for solving recursive domain equations
    X ≅ F(X, X).

    Contents:
    - §1: [IsMixedLocallyContinuous] HB mixin and [MixedLCFunctor] structure
    - §2: Packaged [cont_fun] accessors and equational rewrites
    - §3: Derived properties (joint monotonicity, joint-sup theorem)
    - §4: EP-pair lifting (A&J Proposition 5.2.6)
    - §5: Approximation sequence
    - §6: Abstract [BilimitData] record and existence axiom
    - §7: Consequences (D_inf, ROLL/UNROLL, deflation chain, isomorphism)

    References:
      Abramsky & Jung (1994) §5.2-5.3
      Benton-Kennedy-Varming (2009) §4
      design-decisions.md DD-005
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Theory Require Import
  OrderTheory ChainTheory CPOTheory Products FunctionSpaces EnrichedTheory.

From Stdlib Require Import PeanoNat.


(* ================================================================== *)
(*  §1  IsMixedLocallyContinuous                                      *)
(* ================================================================== *)

HB.mixin Record IsMixedLocallyContinuous (Obj : Type)
    of CPOEnrichedCat Obj & HasMixedEndo Obj := {

  MF_mor_id : forall (A B : Obj),
      MF_mor A A B B (id_mor A) (id_mor B) = id_mor (MF_obj A B);

  MF_mor_comp : forall {A1 A2 A3 B1 B2 B3 : Obj}
      (h : hom A2 A1) (f : hom A3 A2)
      (k : hom B1 B2) (g : hom B2 B3),
      comp _ _ _ (MF_mor A2 A3 B2 B3 f g) (MF_mor A1 A2 B1 B2 h k) =
      MF_mor A1 A3 B1 B3 (comp _ _ _ h f) (comp _ _ _ g k);

  MF_mor_mono_l : forall {A1 A2 B1 B2 : Obj}
      (f f' : hom A2 A1) (g : hom B1 B2),
      f ⊑ f' -> MF_mor A1 A2 B1 B2 f g ⊑ MF_mor A1 A2 B1 B2 f' g;

  MF_mor_mono_r : forall {A1 A2 B1 B2 : Obj}
      (f : hom A2 A1) (g g' : hom B1 B2),
      g ⊑ g' -> MF_mor A1 A2 B1 B2 f g ⊑ MF_mor A1 A2 B1 B2 f g';

  MF_mor_cont_l : forall {A1 A2 B1 B2 : Obj} (g : hom B1 B2),
      @continuous
        (hom A2 A1)
        (hom (MF_obj A1 B1) (MF_obj A2 B2))
        (Build_mono_fun
          (fun f => MF_mor A1 A2 B1 B2 f g)
          (fun f f' Hle => MF_mor_mono_l f f' g Hle));

  MF_mor_cont_r : forall {A1 A2 B1 B2 : Obj} (f : hom A2 A1),
      @continuous
        (hom B1 B2)
        (hom (MF_obj A1 B1) (MF_obj A2 B2))
        (Build_mono_fun
          (fun g => MF_mor A1 A2 B1 B2 f g)
          (fun g g' Hle => MF_mor_mono_r f g g' Hle));
}.

HB.structure Definition MixedLCFunctor :=
  { Obj of CPOEnrichedCat Obj & HasMixedEndo Obj
       & IsMixedLocallyContinuous Obj }.

(* HB resolves MF_mor through MF_Obj, whose carrier sort doesn't
   unify with MixedLCFunctor.sort via canonical structures.
   We define a wrapper with the carrier pinned to MixedLCFunctor. *)
Definition mf_mor {C : MixedLCFunctor.type} {A1 A2 B1 B2 : C}
    (f : hom A2 A1) (g : hom B1 B2) : hom (MF_obj A1 B1) (MF_obj A2 B2) :=
  @MF_mor C A1 A2 B1 B2 f g.

Definition mf_ml {C : MixedLCFunctor.type} {A1 A2 B1 B2 : C}
    (f f' : hom A2 A1) (g : hom B1 B2) (H : f ⊑ f')
    : mf_mor f g ⊑ mf_mor f' g :=
  @MF_mor_mono_l C A1 A2 B1 B2 f f' g H.

Definition mf_mr {C : MixedLCFunctor.type} {A1 A2 B1 B2 : C}
    (f : hom A2 A1) (g g' : hom B1 B2) (H : g ⊑ g')
    : mf_mor f g ⊑ mf_mor f g' :=
  @MF_mor_mono_r C A1 A2 B1 B2 f g g' H.


(* ================================================================== *)
(*  §2  Packaged cont_fun accessors                                   *)
(* ================================================================== *)

Section MFMorContFun.
Context {C : MixedLCFunctor.type} {A1 A2 B1 B2 : C}.

Definition MF_mor_l_cont_fun (g : hom B1 B2)
    : [(hom A2 A1) →c (hom (MF_obj A1 B1) (MF_obj A2 B2))] :=
  Build_cont_fun
    (Build_mono_fun (fun f => mf_mor f g) (fun f f' Hle => mf_ml f f' g Hle))
    (@MF_mor_cont_l C A1 A2 B1 B2 g).

Definition MF_mor_r_cont_fun (f : hom A2 A1)
    : [(hom B1 B2) →c (hom (MF_obj A1 B1) (MF_obj A2 B2))] :=
  Build_cont_fun
    (Build_mono_fun (fun g => mf_mor f g) (fun g g' Hle => mf_mr f g g' Hle))
    (@MF_mor_cont_r C A1 A2 B1 B2 f).

Lemma MF_mor_cont_l_eq (g : hom B1 B2) (cs : chain (hom A2 A1)) :
    mf_mor (⊔ cs) g = ⊔ (map_chain (cf_mono (MF_mor_l_cont_fun g)) cs).
Proof.
  exact (cf_cont (MF_mor_l_cont_fun g) cs).
Qed.

Lemma MF_mor_cont_r_eq (f : hom A2 A1) (ds : chain (hom B1 B2)) :
    mf_mor f (⊔ ds) = ⊔ (map_chain (cf_mono (MF_mor_r_cont_fun f)) ds).
Proof.
  exact (cf_cont (MF_mor_r_cont_fun f) ds).
Qed.

End MFMorContFun.


(* ================================================================== *)
(*  §3  Derived properties                                            *)
(* ================================================================== *)

Section MFDerived.
Context {C : MixedLCFunctor.type}.

Lemma MF_mor_mono {A1 A2 B1 B2 : C}
    (f f' : hom A2 A1) (g g' : hom B1 B2) :
    f ⊑ f' -> g ⊑ g' -> mf_mor f g ⊑ mf_mor f' g'.
Proof.
  intros Hf Hg.
  etransitivity.
  - exact (mf_ml f f' g Hf).
  - exact (mf_mr f' g g' Hg).
Qed.

Definition mf_diag_chain {A1 A2 B1 B2 : C}
    (fs : chain (hom A2 A1)) (gs : chain (hom B1 B2))
    : chain (hom (MF_obj A1 B1) (MF_obj A2 B2)) :=
  Build_chain
    (fun n => mf_mor fs.[n] gs.[n])
    (fun m n Hmn =>
      MF_mor_mono
        (fs.[m]) (fs.[n]) (gs.[m]) (gs.[n])
        (ch_mono fs m n Hmn)
        (ch_mono gs m n Hmn)).

Lemma mf_diag_bound {A1 A2 B1 B2 : C}
    (fs : chain (hom A2 A1)) (gs : chain (hom B1 B2))
    (n m : nat) :
    mf_mor fs.[n] gs.[m] ⊑ ⊔ (mf_diag_chain fs gs).
Proof.
  etransitivity.
  - apply MF_mor_mono.
    + exact (ch_mono fs n (Nat.max n m) (Nat.le_max_l n m)).
    + exact (ch_mono gs m (Nat.max n m) (Nat.le_max_r n m)).
  - exact (sup_upper (mf_diag_chain fs gs) (Nat.max n m)).
Qed.

Theorem MF_mor_joint_sup {A1 A2 B1 B2 : C}
    (fs : chain (hom A2 A1)) (gs : chain (hom B1 B2)) :
    mf_mor (⊔ fs) (⊔ gs) = ⊔ (mf_diag_chain fs gs).
Proof.
  apply le_antisym.
  - rewrite (MF_mor_cont_l_eq (⊔ gs) fs).
    apply sup_least; intro n.
    change (mf_mor fs.[n] (⊔ gs) ⊑ ⊔ (mf_diag_chain fs gs)).
    rewrite (MF_mor_cont_r_eq fs.[n] gs).
    apply sup_least; intro m.
    exact (mf_diag_bound fs gs n m).
  - apply sup_least; intro k.
    apply MF_mor_mono.
    + exact (sup_upper fs k).
    + exact (sup_upper gs k).
Qed.

Lemma MF_mor_id_both (A B : C) :
    mf_mor (id_mor A) (id_mor B) = id_mor (MF_obj A B).
Proof.
  exact (MF_mor_id A B).
Qed.

End MFDerived.


(* ================================================================== *)
(*  §4  EP-pair lifting  (A&J Proposition 5.2.6)                      *)
(* ================================================================== *)

Section EPLift.
Context {C : MixedLCFunctor.type} {A B : C}.

Definition mf_ep_pair (ep : ep_pair A B) : ep_pair (MF_obj A A) (MF_obj B B).
Proof.
  unshelve econstructor.
  - exact (mf_mor (ep_proj ep) (ep_emb ep)).
  - exact (mf_mor (ep_emb ep) (ep_proj ep)).
  - (* Retract: proj o emb = id *)
    transitivity (mf_mor (ep_proj ep ⊚ ep_emb ep) (ep_proj ep ⊚ ep_emb ep)).
    + exact (@MF_mor_comp C A B A A B A
               (ep_proj ep) (ep_emb ep) (ep_emb ep) (ep_proj ep)).
    + rewrite (ep_retract ep).
      exact (MF_mor_id A A).
  - (* Deflation: emb o proj <= id *)
    etransitivity.
    + exact (eq_le _ _ (@MF_mor_comp C B A B B A B
               (ep_emb ep) (ep_proj ep) (ep_proj ep) (ep_emb ep))).
    + etransitivity.
      * apply MF_mor_mono; exact (ep_deflation ep).
      * exact (eq_le _ _ (MF_mor_id_both B B)).
Defined.

End EPLift.

Lemma mf_ep_emb {C : MixedLCFunctor.type} {A B : C} (ep : ep_pair A B) :
    ep_emb (mf_ep_pair ep) = mf_mor (ep_proj ep) (ep_emb ep).
Proof. reflexivity. Qed.

Lemma mf_ep_proj {C : MixedLCFunctor.type} {A B : C} (ep : ep_pair A B) :
    ep_proj (mf_ep_pair ep) = mf_mor (ep_emb ep) (ep_proj ep).
Proof. reflexivity. Qed.

Lemma mf_ep_comp_emb {C : MixedLCFunctor.type} {A B D : C}
    (ep2 : ep_pair B D) (ep1 : ep_pair A B) :
    ep_emb (mf_ep_pair (ep_comp ep2 ep1)) =
    ep_emb (ep_comp (mf_ep_pair ep2) (mf_ep_pair ep1)).
Proof.
  simpl.
  symmetry.
  exact (@MF_mor_comp C A B D A B D
           (ep_proj ep1) (ep_proj ep2) (ep_emb ep1) (ep_emb ep2)).
Qed.

Lemma mf_ep_comp_proj {C : MixedLCFunctor.type} {A B D : C}
    (ep2 : ep_pair B D) (ep1 : ep_pair A B) :
    ep_proj (mf_ep_pair (ep_comp ep2 ep1)) =
    ep_proj (ep_comp (mf_ep_pair ep2) (mf_ep_pair ep1)).
Proof.
  simpl.
  symmetry.
  exact (@MF_mor_comp C D B A D B A
           (ep_emb ep2) (ep_emb ep1) (ep_proj ep2) (ep_proj ep1)).
Qed.


(* ================================================================== *)
(*  §5  Approximation sequence                                        *)
(* ================================================================== *)

Section ApproxSeq.
Context {C : MixedLCFunctor.type}.

Fixpoint mf_approx_obj (D0 : C) (n : nat) : C :=
  match n with
  | O   => D0
  | S n => MF_obj (mf_approx_obj D0 n) (mf_approx_obj D0 n)
  end.

Fixpoint mf_approx_ep (D0 : C) (ep0 : ep_pair D0 (MF_obj D0 D0)) (n : nat)
    : ep_pair (mf_approx_obj D0 n) (mf_approx_obj D0 (S n)) :=
  match n with
  | O   => ep0
  | S n => mf_ep_pair (mf_approx_ep D0 ep0 n)
  end.

Definition mf_approx_epc (D0 : C) (ep0 : ep_pair D0 (MF_obj D0 D0))
    : ep_chain C :=
  {| epc_obj  := mf_approx_obj D0;
     epc_pair := mf_approx_ep D0 ep0; |}.

Definition mf_approx_emb (D0 : C) (ep0 : ep_pair D0 (MF_obj D0 D0)) (n : nat) :=
  ep_emb (mf_approx_ep D0 ep0 n).

Definition mf_approx_proj (D0 : C) (ep0 : ep_pair D0 (MF_obj D0 D0)) (n : nat) :=
  ep_proj (mf_approx_ep D0 ep0 n).

Lemma mf_approx_retract (D0 : C) (ep0 : ep_pair D0 (MF_obj D0 D0)) (n : nat) :
    mf_approx_proj D0 ep0 n ⊚ mf_approx_emb D0 ep0 n =
    id_mor (mf_approx_obj D0 n).
Proof. exact (ep_retract (mf_approx_ep D0 ep0 n)). Qed.

Lemma mf_approx_deflation (D0 : C) (ep0 : ep_pair D0 (MF_obj D0 D0)) (n : nat) :
    mf_approx_emb D0 ep0 n ⊚ mf_approx_proj D0 ep0 n ⊑
    id_mor (mf_approx_obj D0 (S n)).
Proof. exact (ep_deflation (mf_approx_ep D0 ep0 n)). Qed.

End ApproxSeq.


(* ================================================================== *)
(*  §6  Abstract bilimit record and existence axiom                   *)
(* ================================================================== *)

Record BilimitData {C : MixedLCFunctor.type}
    (D0 : C) (ep0 : ep_pair D0 (MF_obj D0 D0)) := {

  bil_lim  : C;

  bil_cone_emb  : forall (n : nat), hom (mf_approx_obj D0 n) bil_lim;
  bil_cone_proj : forall (n : nat), hom bil_lim (mf_approx_obj D0 n);

  bil_cone_retract : forall (n : nat),
      bil_cone_proj n ⊚ bil_cone_emb n = id_mor (mf_approx_obj D0 n);

  bil_cone_deflation : forall (n : nat),
      bil_cone_emb n ⊚ bil_cone_proj n ⊑ id_mor bil_lim;

  bil_cone_compat_emb : forall (n : nat),
      bil_cone_emb (S n) ⊚ mf_approx_emb D0 ep0 n = bil_cone_emb n;

  bil_cone_compat_proj : forall (n : nat),
      bil_cone_proj n = mf_approx_proj D0 ep0 n ⊚ bil_cone_proj (S n);

  bil_id_is_lub : forall (beta : hom bil_lim bil_lim),
      (forall (n : nat), bil_cone_emb n ⊚ bil_cone_proj n ⊑ beta) ->
      id_mor bil_lim ⊑ beta;

  bil_roll   : hom (MF_obj bil_lim bil_lim) bil_lim;
  bil_unroll : hom bil_lim (MF_obj bil_lim bil_lim);

  bil_roll_unroll : bil_roll ⊚ bil_unroll = id_mor bil_lim;
  bil_unroll_roll : bil_unroll ⊚ bil_roll = id_mor (MF_obj bil_lim bil_lim);
}.

Arguments bil_lim              {C D0 ep0}.
Arguments bil_cone_emb         {C D0 ep0}.
Arguments bil_cone_proj        {C D0 ep0}.
Arguments bil_cone_retract     {C D0 ep0}.
Arguments bil_cone_deflation   {C D0 ep0}.
Arguments bil_cone_compat_emb  {C D0 ep0}.
Arguments bil_cone_compat_proj {C D0 ep0}.
Arguments bil_id_is_lub        {C D0 ep0}.
Arguments bil_roll             {C D0 ep0}.
Arguments bil_unroll           {C D0 ep0}.
Arguments bil_roll_unroll      {C D0 ep0}.
Arguments bil_unroll_roll      {C D0 ep0}.

(* Bilimit existence axiom.
   Proof obligation: construct D_inf as the coherent sub-CPO of
   the omega-product CPO Pi_n D_n.  See Benton-Kennedy-Varming (2009) §4 and
   A&J §3.3.7.  Requires omega-product CPO not yet in this library. *)
Axiom bilimit_exists :
  forall {C : MixedLCFunctor.type} (D0 : C)
         (ep0 : ep_pair D0 (MF_obj D0 D0)),
    BilimitData D0 ep0.


(* ================================================================== *)
(*  §7  Consequences of BilimitData                                   *)
(* ================================================================== *)

Section BilimitCorollaries.
Context {C : MixedLCFunctor.type} (D0 : C)
        (ep0 : ep_pair D0 (MF_obj D0 D0)).

Let BD := bilimit_exists D0 ep0.

Definition D_inf  : C := bil_lim BD.
Definition ROLL   : hom (MF_obj D_inf D_inf) D_inf := bil_roll BD.
Definition UNROLL : hom D_inf (MF_obj D_inf D_inf) := bil_unroll BD.

Theorem bil_iso_roll_unroll : ROLL ⊚ UNROLL = id_mor D_inf.
Proof. exact (bil_roll_unroll BD). Qed.

Theorem bil_iso_unroll_roll : UNROLL ⊚ ROLL = id_mor (MF_obj D_inf D_inf).
Proof. exact (bil_unroll_roll BD). Qed.

(* Deflation retractions form an increasing chain. *)

Lemma bil_retract_step (n : nat) :
    bil_cone_emb BD n ⊚ bil_cone_proj BD n ⊑
    bil_cone_emb BD (S n) ⊚ bil_cone_proj BD (S n).
Proof.
  rewrite <- (bil_cone_compat_emb BD n).
  rewrite (bil_cone_compat_proj BD n).
  rewrite (@comp_assoc C).
  rewrite <- (@comp_assoc C _ _ _ _
    (mf_approx_emb D0 ep0 n) (mf_approx_proj D0 ep0 n) (bil_cone_proj BD (S n))).
  etransitivity.
  - apply comp_mono_l.
    apply comp_mono_r.
    exact (mf_approx_deflation D0 ep0 n).
  - rewrite (@comp_id_l C).
    exact (@le_refl (hom _ _) _).
Qed.

Lemma bil_retract_chain_mono :
    forall m n, m <= n ->
    bil_cone_emb BD m ⊚ bil_cone_proj BD m ⊑
    bil_cone_emb BD n ⊚ bil_cone_proj BD n.
Proof.
  intros m n Hmn.
  induction Hmn.
  - exact (@le_refl (hom _ _) _).
  - etransitivity; [exact IHHmn | exact (bil_retract_step m0)].
Qed.

Definition bil_defl_chain : chain (hom D_inf D_inf) :=
  Build_chain
    (fun n => bil_cone_emb BD n ⊚ bil_cone_proj BD n)
    (fun m n Hmn => bil_retract_chain_mono m n Hmn).

Lemma bil_sup_deflations : ⊔ bil_defl_chain = id_mor D_inf.
Proof.
  apply le_antisym.
  - apply sup_least; intro n.
    exact (bil_cone_deflation BD n).
  - apply bil_id_is_lub.
    intro n.
    exact (sup_upper bil_defl_chain n).
Qed.

(* The isomorphism D_inf ~= F(D_inf, D_inf). *)

Definition bil_lim_iso : ep_pair D_inf (MF_obj D_inf D_inf).
Proof.
  unshelve econstructor.
  - exact UNROLL.
  - exact ROLL.
  - exact bil_iso_roll_unroll.
  - rewrite bil_iso_unroll_roll. exact (@le_refl (hom _ _) _).
Defined.

Definition bil_lim_iso_inv : ep_pair (MF_obj D_inf D_inf) D_inf.
Proof.
  unshelve econstructor.
  - exact ROLL.
  - exact UNROLL.
  - exact bil_iso_unroll_roll.
  - rewrite bil_iso_roll_unroll. exact (@le_refl (hom _ _) _).
Defined.

Definition bil_cone_ep (n : nat) : ep_pair (mf_approx_obj D0 n) D_inf :=
  {| ep_emb      := bil_cone_emb BD n;
     ep_proj     := bil_cone_proj BD n;
     ep_retract  := bil_cone_retract BD n;
     ep_deflation := bil_cone_deflation BD n; |}.

End BilimitCorollaries.
