(*  FunctionSpaces

    Phase 0: The continuous-function-space CPO.

    This is [src/theory/FunctionSpaces.v].

    Imports:
      [src/structures/Order.v]     — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]       — CPO, PointedCPO, HasSup, IsCPO, continuous
      [src/structures/Morphisms.v] — cont_fun, cont_comp, cont_id
      [src/theory/OrderTheory.v]   — pequiv_eq, eq_le, mono_fun_ext
      [src/theory/ChainTheory.v]   — coherent_family, diag_chain
      [src/theory/CPOTheory.v]     — sup lemmas, cont_fun_ext, continuous_of_le,
                                     mono_sup_le, admissible
      [src/theory/Products.v]      — product CPO, π₁, π₂, cont_pair

    Summary
    =======
    For two CPOs [D] and [E], the type [D →c E] of Scott-continuous
    functions becomes a CPO under the pointwise order:

        f ⊑ g  ↔  ∀ x, f x ⊑ g x

    The supremum of a chain [fs : chain [D →c E]] is computed
    pointwise:

        (⊔ fs) x = ⊔ (map_chain (eval_mono x) fs)

    The proof that [⊔ fs] is Scott-continuous uses the _diagonal lemma_
    from [ChainTheory.v]: given a chain [c : chain D], the family
    [n ↦ map_chain (eval_mono (c.[k])) fs] is coherent (because [fs] is
    a chain in the pointwise order), so the diagonal chain construction
    yields [⊔ (⊔ fs ∘ c) = ⊔ diag].

    Additionally, this file proves:
    - Evaluation [eval : [D →c E] × D →c E] is continuous.
    - Currying: if [f : C × D →c E] then [curry f : C →c [D →c E]].
    - Uncurrying: if [f : C →c [D →c E]] then [uncurry f : C × D →c E].
    - The curry–uncurry bijection (the exponential adjunction).

    Together these establish that the category of CPOs and continuous maps
    is cartesian closed.

    Contents:
    - §1  Pointwise order on [D →c E] — HB instance registrations
    - §2  Pointwise sup — [HasSup] and [IsCPO] instances
    - §3  Evaluation map
    - §4  Currying and uncurrying
    - §5  Exponential adjunction laws
    - §6  FIXP — the continuous fixed-point operator

    Phase coverage:
      Phase 0 — all sections
      Phase 1 — §3-§6 used in [EnrichedTheory.v], [PCF_Denotational.v]
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory ChainTheory CPOTheory Products FixedPoints.

From Stdlib Require Import FunctionalExtensionality ProofIrrelevance.
From Stdlib Require Import PeanoNat.


(* ================================================================== *)
(*   §1  Pointwise order on [D →c E]                            *)
(* ================================================================== *)
(*
    The pointwise order on [D →c E]:
        f ⊑ g  ↔  ∀ x : D, f x ⊑ g x
*)

Section FunOrder.
Context {D E : CPO.type}.

Definition fun_le (f g : [D →c E]) : Prop :=
  forall (x : D), f x ⊑ g x.

Lemma fun_le_refl (f : [D →c E]) : fun_le f f.
Proof.
  intro x; apply le_refl.
Qed.

Lemma fun_le_trans (f g h : [D →c E]) :
  fun_le f g -> fun_le g h -> fun_le f h.
Proof.
  intros Hfg Hgh x.
  exact (le_trans _ _ _ (Hfg x) (Hgh x)).
Qed.

Lemma fun_le_antisym (f g : [D →c E]) :
  fun_le f g -> fun_le g f -> f = g.
Proof.
  intros Hfg Hgf.
  apply cont_fun_ext; intro x.
  exact (le_antisym _ _ (Hfg x) (Hgf x)).
Qed.

End FunOrder.


(*
    Register the order structure on [D →c E] for all [D E : CPO.type].
    After these instances, [⊑] on [D →c E] denotes the pointwise order.
*)
HB.instance Definition fun_HasLe {D E : CPO.type} :=
  HasLe.Build [D →c E] fun_le.

HB.instance Definition fun_IsPreorder {D E : CPO.type} :=
  IsPreorder.Build [D →c E] fun_le_refl fun_le_trans.

HB.instance Definition fun_IsPartialOrder {D E : CPO.type} :=
  IsPartialOrder.Build [D →c E] fun_le_antisym.


(* ================================================================== *)
(*   §2  Pointwise sup                                                 *)
(* ================================================================== *)
(*
    The sup of a chain [fs : chain [D →c E]] is computed pointwise.
    Given a point [x : D], we extract the chain [n ↦ (fs.[n]) x] in E,
    and define [(⊔ fs) x = ⊔ (n ↦ (fs.[n]) x)].

    The key difficulty is showing that this pointwise sup is itself
    Scott-continuous, which requires the diagonal lemma.
*)

Section FunSup.
Context {D E : CPO.type}.

(*
    [eval_at_mono x] is the monotone function that evaluates a continuous
    function at [x].  This maps [[D →c E] → E] and is monotone
    because [fs] is ordered pointwise.
*)
Definition eval_at_mono (x : D) : mono_fun [D →c E] E :=
  Build_mono_fun
    (fun (f : [D →c E]) => f x)
    (fun (f g : [D →c E]) (Hfg : fun_le f g) => Hfg x).

(*
    Given a chain of continuous functions and a point, form the chain
    of values at that point.
*)
Definition pointwise_chain (fs : chain [D →c E]) (x : D) : chain E :=
  map_chain (eval_at_mono x) fs.

Lemma pointwise_chain_index (fs : chain [D →c E]) (x : D) (n : nat) :
  (pointwise_chain fs x).[n] = fs.[n] x.
Proof.
  reflexivity.
Qed.

(*
    The pointwise-sup function.  Given a chain [fs] of continuous functions,
    for each [x] we take the sup of the values chain.
*)
Definition fun_sup_fun (fs : chain [D →c E]) : D -> E :=
  fun x => ⊔ (pointwise_chain fs x).

(*
    The pointwise-sup function is monotone.
    Proof: if [x ⊑ y] then [fs.[n] x ⊑ fs.[n] y] (each [fs.[n]] is monotone),
    so [⊔ (fs.[_] x) ⊑ ⊔ (fs.[_] y)] by [sup_mono].
*)
Lemma fun_sup_mono (fs : chain [D →c E]) :
  monotone D E (fun_sup_fun fs).
Proof.
  intros x y Hxy.
  apply sup_mono; intros n.
  simpl.
  apply (mf_mono (cf_mono (fs.[n]))).
  exact Hxy.
Qed.

Definition fun_sup_mono_fun (fs : chain [D →c E]) : mono_fun D E :=
  Build_mono_fun (fun_sup_fun fs) (fun_sup_mono fs).

(*
    The pointwise-sup function is Scott-continuous.

    This is the core technical result.  Given a chain [c : chain D], we must
    show:
        (⊔ fs)(⊔ c) = ⊔ (map_chain (fun_sup_mono_fun fs) c)

    i.e.:
        ⊔_n (fs.[n] (⊔ c)) = ⊔_k (⊔_n (fs.[n] (c.[k])))

    Both sides equal the double supremum ⊔_{n,k} (fs.[n] (c.[k])),
    which we access via the diagonal lemma on the coherent family
    [F k n = fs.[n] (c.[k])].

    Proof strategy:
    (1) Each [fs.[n]] is continuous, so [fs.[n] (⊔ c) = ⊔_k (fs.[n] (c.[k]))].
        The LHS becomes ⊔_n ⊔_k (fs.[n] (c.[k])).
    (2) The family [F_k = (n ↦ fs.[n] (c.[k]))] is coherent (pointwise ordering
        of [fs] at each [c.[k]]).
    (3) Moreover, for fixed [n], [k ↦ fs.[n] (c.[k])] is a chain (monotonicity
        of [fs.[n]]).
    (4) We use [continuous_of_le]: it suffices to show
        (⊔ fs)(⊔ c) ⊑ ⊔ (map_chain (fun_sup_mono_fun fs) c)
        since the reverse is free from monotonicity.
*)

(*
    Helper: the family [k ↦ pointwise_chain fs (c.[k])] is coherent.
    Coherence means: for [m ≤ n], [fs.[j] (c.[m]) ⊑ fs.[j] (c.[n])].
    This follows from monotonicity of each [fs.[j]].
*)
Lemma pointwise_family_coherent (fs : chain [D →c E]) (c : chain D) :
  coherent_family (fun k => pointwise_chain fs (c.[k])).
Proof.
  intros m n j Hmn.
  simpl.
  apply (mf_mono (cf_mono (fs.[j]))).
  exact (ch_mono c m n Hmn).
Qed.

(*
    The key inequality: (⊔ fs)(⊔ c) ⊑ ⊔_k ((⊔ fs)(c.[k])).

    Proof:
    LHS = ⊔_n (fs.[n] (⊔ c))                      [definition of fun_sup_fun]
        = ⊔_n (⊔_k (fs.[n] (c.[k])))               [continuity of fs.[n]]

    For each n: ⊔_k (fs.[n] (c.[k])) ⊑ ⊔_k (⊔_j (fs.[j] (c.[k])))
                                      = ⊔_k ((⊔ fs)(c.[k]))
    because fs.[n] (c.[k]) ⊑ ⊔_j (fs.[j] (c.[k])) by sup_upper at j=n.

    Then LHS ⊑ RHS by sup_least over n.
*)
Lemma fun_sup_cont_le (fs : chain [D →c E]) (c : chain D) :
  fun_sup_fun fs (⊔ c) ⊑ ⊔ (map_chain (fun_sup_mono_fun fs) c).
Proof.
  unfold fun_sup_fun.
  apply sup_least; intros n.
  simpl.
  rewrite (cf_cont (fs.[n]) c).
  apply sup_least; intros k.
  apply le_trans with (⊔ (pointwise_chain fs (c.[k]))).
  - exact (sup_upper (pointwise_chain fs (c.[k])) n).
  - exact (sup_upper (map_chain (fun_sup_mono_fun fs) c) k).
Qed.

Lemma fun_sup_continuous (fs : chain [D →c E]) :
  continuous (fun_sup_mono_fun fs).
Proof.
  apply continuous_of_le.
  exact (fun_sup_cont_le fs).
Qed.

(* The pointwise sup as a [cont_fun]. *)
Definition fun_sup (fs : chain [D →c E]) : [D →c E] :=
  Build_cont_fun (fun_sup_mono_fun fs) (fun_sup_continuous fs).

(* The pointwise sup unfolds correctly. *)
Lemma fun_sup_apply (fs : chain [D →c E]) (x : D) :
  fun_sup fs x = ⊔ (pointwise_chain fs x).
Proof.
  reflexivity.
Qed.

(*
    [fun_sup fs] is an upper bound of [fs]:
    for each [n] and [x], [fs.[n] x ⊑ (⊔ fs) x] by [sup_upper].
*)
Lemma fun_sup_upper (fs : chain [D →c E]) (n : nat) :
  fs.[n] ⊑ fun_sup fs.
Proof.
  intro x; simpl.
  exact (sup_upper (pointwise_chain fs x) n).
Qed.

(*
    [fun_sup fs] is the least upper bound:
    if [g] is an upper bound of [fs], then for each [x],
    [fs.[n] x ⊑ g x] for all [n], so [(⊔ fs) x = ⊔(fs.[_] x) ⊑ g x].
*)
Lemma fun_sup_least (fs : chain [D →c E]) (g : [D →c E]) :
  (forall n, fs.[n] ⊑ g) -> fun_sup fs ⊑ g.
Proof.
  intros Hub x; simpl.
  apply sup_least; intros n.
  exact (Hub n x).
Qed.

End FunSup.


(*
    Register [D →c E] as a CPO via the pointwise sup.
*)
HB.instance Definition fun_HasSup {D E : CPO.type} :=
  HasSup.Build [D →c E] fun_sup.

HB.instance Definition fun_IsCPO {D E : CPO.type} :=
  IsCPO.Build [D →c E] fun_sup_upper fun_sup_least.


(*
    PointedCPO instance: if [E] is a pointed CPO, then [D →c E] is
    pointed with bottom = the constant-⊥ function.
*)
Section FunPointed.
Context {D : CPO.type} {E : PointedCPO.type}.

Definition fun_bottom_mono : mono_fun D E :=
  Build_mono_fun (fun _ => ⊥) (fun _ _ _ => le_refl ⊥).

Lemma fun_bottom_continuous : continuous fun_bottom_mono.
Proof.
  apply continuous_of_le.
  intro c. apply bottom_least.
Qed.

Definition fun_bottom : [D →c E] :=
  Build_cont_fun fun_bottom_mono fun_bottom_continuous.

Lemma fun_bottom_least (f : [D →c E]) : fun_bottom ⊑ f.
Proof.
  intro x; simpl.
  apply bottom_least.
Qed.

End FunPointed.

HB.instance Definition fun_HasBottom {D : CPO.type} {E : PointedCPO.type} :=
  HasBottom.Build [D →c E] (fun_bottom (D:=D) (E:=E)).

HB.instance Definition fun_IsPointed {D : CPO.type} {E : PointedCPO.type} :=
  IsPointed.Build [D →c E] (fun_bottom_least (D:=D) (E:=E)).


(* ================================================================== *)
(*   §3  Evaluation map                                                *)
(* ================================================================== *)
(*
    The evaluation map [eval : [D →c E] × D → E] sends [(f, x)]
    to [f x].  It is Scott-continuous as a function of the product.

    Proof of continuity:
      Given a chain [c : chain ([D →c E] × D)], let
      [fs := map_chain fst_mono c] and [ds := map_chain snd_mono c].
      Then eval(⊔ c) = (⊔ fs)(⊔ ds) = ⊔ (pointwise_chain fs (⊔ ds)).
      We reduce to showing ⊔ (pointwise_chain fs (⊔ ds)) ⊑ ⊔ (eval ∘ c)
      using the double-sup argument: for each n and k we have
      fs.[n](ds.[k]) ⊑ eval(c.[max n k]) by the chain property.
*)

Open Scope type_scope.

Section EvalMap.
Context {D E : CPO.type}.

Definition eval_fun (p : [D →c E] * D) : E :=
  (fst p) (snd p).

Lemma eval_mono : monotone ([D →c E] * D) E eval_fun.
Proof.
  intros [f x] [g y] [Hfg Hxy]; simpl in *.
  apply le_trans with (f y).
  - apply (mf_mono (cf_mono f)). exact Hxy.
  - exact (Hfg y).
Qed.

Definition eval_mono_fun : mono_fun ([D →c E] * D) E :=
  Build_mono_fun eval_fun eval_mono.

(*
    Continuity of eval.

    The goal is: eval_mono_fun (⊔ c) ⊑ ⊔ (map_chain eval_mono_fun c).
    LHS = (⊔ fs)(⊔ ds) = ⊔ (pointwise_chain fs (⊔ ds)), where
    fs := map_chain fst_mono c and ds := map_chain snd_mono c.
    We [change] to this explicit form, then use the double-sup argument.

    For each n and k, with m = max n k:
      fs.[n](ds.[k]) ⊑ fs.[n](ds.[m])              [ds is a chain, k ≤ m]
                    ⊑ fs.[m](ds.[m])               [fs is a chain, n ≤ m, pointwise]
                    = eval_fun(c.[m])
                    ⊑ ⊔ (map_chain eval_mono_fun c)  [sup_upper]
*)
Lemma eval_continuous : continuous eval_mono_fun.
Proof.
  apply continuous_of_le; intros c.
  set (fs := map_chain fst_mono c : chain [D →c E]).
  set (ds := map_chain snd_mono c : chain D).
  apply sup_least; intros n.
  simpl.
  (* fs.[n](⊔ ds) ⊑ ⊔ (map_chain eval_mono_fun c) *)
  (* By cf_cont, LHS = ⊔_k fs.[n](ds.[k]) *)
  (* For each k, fs.[n](ds.[k]) ⊑ eval_fun(c.[max n k]) ⊑ ⊔ (map_chain eval_mono_fun c) *)
  apply le_trans with (⊔ (map_chain (cf_mono (fs.[n])) ds)).
  - exact (eq_ind _ (fun z => z ⊑ _) (le_refl _) _ (eq_sym (cf_cont (fs.[n]) ds))).
  - apply sup_least; intros k.
    simpl.
    set (m := Nat.max n k).
    apply le_trans with (eval_fun (c.[m])).
    + apply le_trans with (cf_mono (fs.[n]) (ds.[m])).
      * apply (mf_mono (cf_mono (fs.[n]))).
        apply (ch_mono c k m). apply Nat.le_max_r.
      * exact ((ch_mono (map_chain fst_mono c) n m (Nat.le_max_l n k)) (ds.[m])).
    + apply (sup_upper (map_chain eval_mono_fun c)).
Qed.

Definition cont_eval : [[D →c E] * D →c E] :=
  Build_cont_fun eval_mono_fun eval_continuous.

(* Computation rule: [cont_eval (f, x) = f x]. *)
Lemma cont_eval_apply (f : [D →c E]) (x : D) :
  cont_eval (f, x) = f x.
Proof.
  reflexivity.
Qed.

End EvalMap.


(* ================================================================== *)
(*   §4  Currying and uncurrying                                       *)
(* ================================================================== *)
(*
    Currying: given [f : C × D →c E], produce [curry f : C →c [D →c E]].

    For each [c : C], [(curry f) c] must be a continuous function [D → E].
    We define it as [fun d => f (c, d)].  Continuity in [d] follows from
    continuity of [f] applied to a chain with constant first component.

    Then [curry f] must be continuous as a function [C → [D →c E]],
    where the codomain has the pointwise order.  For a chain [cs] in [C]:
      (curry f)(⊔ cs) = fun d => f(⊔ cs, d)
    and we need this to equal
      ⊔_n (curry f)(cs.[n]) = fun d => ⊔_n f(cs.[n], d)
    which follows from continuity of [f] in the first argument.
*)

Section CurryUncurry.
Context {C D E : CPO.type}.

(* --- Curry --- *)

(*
    For a fixed [c : C], the function [d ↦ f(c, d)] is monotone.
*)
Definition curry_inner_mono (f : [C * D →c E]) (c : C) : mono_fun D E :=
  Build_mono_fun
    (fun d => f (c, d))
    (fun d1 d2 Hd =>
      mf_mono (cf_mono f) (c, d1) (c, d2) (conj (le_refl c) Hd)).

(*
    For a fixed [c : C], the function [d ↦ f(c, d)] is continuous.

    Proof: form the chain [paired n = (c, dc.[n])].  Its sup is (c, ⊔ dc)
    since the first component is constant.  Continuity of [f] gives
    f(c, ⊔ dc) = f(⊔ paired) = ⊔ (map_chain f paired) = ⊔_n f(c, dc.[n]).
*)
Lemma curry_inner_cont (f : [C * D →c E]) (c : C) :
  continuous (curry_inner_mono f c).
Proof.
  apply continuous_of_le; intros dc.
  set (paired := Build_chain
    (fun n => (c, dc.[n]) : C * D)
    (fun m n Hmn => conj (le_refl c) (ch_mono dc m n Hmn)) : chain (C * D)).
  (* Goal: f(c, ⊔ dc) ⊑ ⊔ (map_chain (curry_inner_mono f c) dc) *)
  (* Strategy: go through f(⊔ paired) using continuity of f *)
  apply le_trans with (cf_mono f (⊔ paired)).
  { 
    apply (mf_mono (cf_mono f)).
    split.
    - exact (sup_upper (map_chain fst_mono paired) 0).
    - apply sup_mono; intros n; exact (le_refl (dc.[n])). 
  }
  apply le_trans with (⊔ (map_chain (cf_mono f) paired)).
  { exact (eq_ind _ (fun z => z ⊑ _) (le_refl _) _ (eq_sym (cf_cont f paired))). }
  apply sup_mono; intros n. exact (le_refl _).
Qed.

Definition curry_val (f : [C * D →c E]) (c : C) : [D →c E] :=
  Build_cont_fun (curry_inner_mono f c) (curry_inner_cont f c).

(*
    [curry_val f] is monotone as a function [C → [D →c E]]:
    if [c1 ⊑ c2] then [f(c1, d) ⊑ f(c2, d)] for all [d] (by monotonicity of f).
*)
Lemma curry_mono (f : [C * D →c E]) :
  monotone C [D →c E] (curry_val f).
Proof.
  intros c1 c2 Hc d; simpl.
  apply (mf_mono (cf_mono f)).
  exact (conj Hc (le_refl d)).
Qed.

Definition curry_mono_fun (f : [C * D →c E]) : mono_fun C [D →c E] :=
  Build_mono_fun (curry_val f) (curry_mono f).

(*
    [curry_val f] is continuous: for a chain [cs] in [C],
    [curry_val f (⊔ cs) = ⊔_n (curry_val f (cs.[n]))]
    in the pointwise order on [D →c E].

    This means: for all [d],
      f(⊔ cs, d) = ⊔_n f(cs.[n], d).

    Proof: fix [d].  The chain [(cs.[0], d), (cs.[1], d), …] in [C × D]
    has sup [(⊔ cs, d)], and continuity of [f] gives the result.
*)
Lemma curry_continuous (f : [C * D →c E]) :
  continuous (curry_mono_fun f).
Proof.
  apply continuous_of_le; intros cs.
  intro d; simpl.
  set (paired := Build_chain
    (fun n => (cs.[n], d) : C * D)
    (fun m n Hmn => conj (ch_mono cs m n Hmn) (le_refl d)) : chain (C * D)).
  (* Goal: f(⊔ cs, d) ⊑ ⊔_n f(cs.[n], d) *)
  (* Strategy: go through f(⊔ paired) *)
  apply le_trans with (cf_mono f (⊔ paired)).
  { apply (mf_mono (cf_mono f)).
    split.
    - apply sup_mono; intros n; exact (le_refl (cs.[n])).
    - exact (sup_upper (map_chain snd_mono paired) 0). 
  }
  apply le_trans with (⊔ (map_chain (cf_mono f) paired)).
  { exact (eq_ind _ (fun z => z ⊑ _) (le_refl _) _ (eq_sym (cf_cont f paired))). }
  apply sup_least; intros n. simpl.
  apply le_trans with (⊔ (pointwise_chain (map_chain (curry_mono_fun f) cs) d)).
  + apply (sup_upper (pointwise_chain (map_chain (curry_mono_fun f) cs) d) n).
  + apply le_refl.
Qed.

Definition cont_curry (f : [C * D →c E]) : [C →c [D →c E]] :=
  Build_cont_fun (curry_mono_fun f) (curry_continuous f).

(*
    Computation rule: [(curry f) c d = f (c, d)].
*)
Lemma cont_curry_apply (f : [C * D →c E]) (c : C) (d : D) :
  cont_curry f c d = f (c, d).
Proof.
  reflexivity.
Qed.


(* --- Uncurry --- *)

(*
    Uncurrying: given [f : C →c [D →c E]], produce
    [uncurry f : C × D →c E] defined by [uncurry f (c, d) = f c d].
*)

Definition uncurry_fun (f : [C →c [D →c E]]) : C * D -> E :=
  fun p => (f (fst p)) (snd p).

Lemma uncurry_mono (f : [C →c [D →c E]]) :
  monotone (C * D) E (uncurry_fun f).
Proof.
  intros [c1 d1] [c2 d2] [Hc Hd]; simpl in *.
  apply le_trans with (f c1 d2).
  - apply (mf_mono (cf_mono (f c1))). exact Hd.
  - exact ((mf_mono (cf_mono f) c1 c2 Hc : f c1 ⊑ f c2) d2).
Qed.

Definition uncurry_mono_fun (f : [C →c [D →c E]]) : mono_fun (C * D) E :=
  Build_mono_fun (uncurry_fun f) (uncurry_mono f).

(*
    Uncurry preserves continuity.

    The cleanest proof: [uncurry f = eval ∘ (f × id)].  Since both [eval]
    and [cont_prod_map f (cont_id D)] are continuous, so is their composite.
    We verify the equality of underlying functions by [reflexivity].
*)
Lemma uncurry_continuous (f : [C →c [D →c E]]) :
  continuous (uncurry_mono_fun f).
Proof.
  set (g := cont_comp cont_eval (cont_prod_map f (cont_id D))).
  assert (Heq : uncurry_mono_fun f = cf_mono g).
  { apply mono_fun_ext. intros [c d]. reflexivity. }
  rewrite Heq. exact (cf_cont g).
Qed.

Definition cont_uncurry (f : [C →c [D →c E]]) : [C * D →c E] :=
  Build_cont_fun (uncurry_mono_fun f) (uncurry_continuous f).

(*
    Computation rule: [(uncurry f) (c, d) = f c d].
*)
Lemma cont_uncurry_apply (f : [C →c [D →c E]]) (c : C) (d : D) :
  cont_uncurry f (c, d) = f c d.
Proof.
  reflexivity.
Qed.

End CurryUncurry.


(* ================================================================== *)
(*   §5  Exponential adjunction laws                                   *)
(* ================================================================== *)
(*
    The curry–uncurry pair forms an isomorphism:
      curry ∘ uncurry = id
      uncurry ∘ curry = id

    This establishes the exponential adjunction:
      Hom(C × D, E) ≅ Hom(C, E^D)
    in the category of CPOs and continuous maps.
*)

Section ExpAdjunction.
Context {C D E : CPO.type}.

(*
    curry (uncurry f) = f
    i.e., for all c and d: curry(uncurry f) c d = f c d.
*)
Lemma curry_uncurry (f : [C →c [D →c E]]) :
  cont_curry (cont_uncurry f) = f.
Proof.
  apply cont_fun_ext; intros c.
  apply cont_fun_ext; intros d.
  reflexivity.
Qed.

(*
    uncurry (curry f) = f
    i.e., for all (c,d): uncurry(curry f) (c,d) = f(c,d).
*)
Lemma uncurry_curry (f : [C * D →c E]) :
  cont_uncurry (cont_curry f) = f.
Proof.
  apply cont_fun_ext; intros [c d].
  reflexivity.
Qed.

(*
    Curry is natural in C: [curry(f ∘ (g × id)) = (curry f) ∘ g].
*)
Lemma curry_comp {C' : CPO.type} (f : [C * D →c E]) (g : [C' →c C]) :
  cont_curry (cont_comp f (cont_prod_map g (cont_id D))) =
  cont_comp (cont_curry f) g.
Proof.
  apply cont_fun_ext; intros c'.
  apply cont_fun_ext; intros d.
  reflexivity.
Qed.

(*
    Eval law: [eval ∘ (curry f × id) = f].
*)
Lemma eval_curry (f : [C * D →c E]) :
  cont_comp cont_eval (cont_prod_map (cont_curry f) (cont_id D)) = f.
Proof.
  apply cont_fun_ext; intros [c d].
  reflexivity.
Qed.

(*
    The universal property: [curry] is the unique map making [eval ∘ (h × id) = f].
*)
Lemma curry_unique (f : [C * D →c E]) (h : [C →c [D →c E]]) :
  (forall c d, cont_eval (h c, d) = f (c, d)) ->
  h = cont_curry f.
Proof.
  intros Heq.
  apply cont_fun_ext; intros c.
  apply cont_fun_ext; intros d.
  exact (Heq c d).
Qed.

End ExpAdjunction.
Close Scope type_scope.

(* ================================================================== *)
(*   Miscellaneous derived lemmas                                      *)
(* ================================================================== *)

Section FunMisc.
Context {D E : CPO.type}.

(*
    The sup of a constant chain of functions is the function itself.
*)
Lemma fun_sup_const (f : [D →c E]) :
  ⊔ (const_chain f) = f.
Proof.
  exact (sup_const_chain f).
Qed.

(*
    Pointwise sup commutes with application.
    (Re-export of [fun_sup_apply] for downstream convenience.)
*)
Lemma sup_apply (fs : chain [D →c E]) (x : D) :
  (⊔ fs) x = ⊔ (pointwise_chain fs x).
Proof.
  reflexivity.
Qed.

(*
    The sup of a chain of functions applied to a chain element is bounded
    by the overall sup at the overall sup of the argument chain.
*)
Lemma sup_chain_apply_le (fs : chain [D →c E]) (c : chain D) (n : nat) :
  fs.[n] (c.[n]) ⊑ (⊔ fs) (⊔ c).
Proof.
  apply le_trans with ((⊔ fs) (c.[n])).
  - exact (fun_sup_upper fs n (c.[n])).
  - apply (mf_mono (cf_mono (⊔ fs))).
    exact (sup_upper c n).
Qed.

End FunMisc.


(* ================================================================== *)
(*   §6  FIXP — the continuous fixed-point operator                    *)
(* ================================================================== *)
(*
    For a pointed CPO [D], the Kleene fixed-point operator

        fixp : [D →c D] → D

    (defined in [FixedPoints.v]) is itself a Scott-continuous map
    from the function-space CPO [[D →c D]] to [D].  The packaged
    continuous version is

        FIXP : [[D →c D] →c D]

    Monotonicity of [fixp] is already proved in [FixedPoints.v] as
    [fixp_mono].

    The continuity proof shows that [⊔ₙ fixp (fₙ)] is a pre-fixed-point
    of [⊔ₙ fₙ].  Then [fixp_least] gives [fixp (⊔ₙ fₙ) ⊑ ⊔ₙ fixp (fₙ)],
    which (combined with the monotonicity direction) establishes equality.

    The key step uses continuity of each [fₙ] and the fixed-point
    identity [fₙ (fixp fₙ) = fixp fₙ] to show the pre-fixed-point
    inequality.

    Reference: A&J §2.1.3 Proposition 2.1.18; Benton-Kennedy [FIXP].
*)

Section FIXP.
Context {D : PointedCPO.type}.

(*
    Wrap [fixp] as a monotone function on the function-space CPO.
    Monotonicity: [fixp_mono] from [FixedPoints.v].
*)
Definition fixp_mono_fun : mono_fun [D →c D] D :=
  Build_mono_fun fixp (fun f g Hle => fixp_mono f g Hle).

(*
    The chain of fixpoints: given a chain [fs] of endomorphisms,
    [fixp_chain fs] is the chain [n ↦ fixp (fs.[n])] in [D].
*)
Definition fixp_chain (fs : chain [D →c D]) : chain D :=
  map_chain fixp_mono_fun fs.

(*
    Key lemma: [⊔ₙ fixp (fₙ)] is a pre-fixed-point of [⊔ₙ fₙ].

    i.e., [(⊔ fs) (⊔ fixp_chain) ⊑ ⊔ fixp_chain].

    Proof:

    1.  [(⊔ fs) y = ⊔ₙ (fₙ y)] by the pointwise sup of functions.
    2.  For each [n], by continuity of [fₙ]:
          [fₙ y = fₙ (⊔ₘ fixp fₘ) = ⊔ₘ fₙ (fixp fₘ)].
    3.  For each pair [(n, m)]:
          [fₙ (fixp fₘ) ⊑  f_{max(n,m)} (fixp f_{max(n,m)})  =  fixp f_{max(n,m)}  ⊑  y]
        using the chain monotonicity of [fs], [fixp_mono],
        monotonicity of continuous functions, and the fixed-point identity.
    4.  By [sup_least] twice, [⊔ₙ ⊔ₘ fₙ (fixp fₘ) ⊑ y].
*)
(*
    Bridge lemma: decompose [⊔ fs] applied at a point into [sup_least]
    over the pointwise chain.  This avoids the HB structure-unification
    issue that arises when [D : PointedCPO.type] is coerced to [CPO.type]
    inside the function-space construction.

    Note: [eval_continuous] (§3) uses the same [eq_ind] technique.
*)
Lemma fun_sup_app_le (fs : chain [D →c D]) (x : D) (y : D) :
    (forall n, fs.[n] x ⊑ y) -> (⊔ fs) x ⊑ y.
Proof.
  intro H. exact (sup_least (pointwise_chain fs x) y H).
Qed.

(*
    Bridge lemma: decompose [f (⊔ c)] into [sup_least] over the image
    chain using [cf_cont], again via [eq_ind] to avoid HB mismatch.
*)
Lemma cf_app_sup_le (f : [D →c D]) (c : chain D) (y : D) :
    (forall n, f (c.[n]) ⊑ y) -> f (⊔ c) ⊑ y.
Proof.
  intro H.
  exact (eq_ind _ (fun z => z ⊑ y)
           (sup_least (map_chain (cf_mono f) c) y H)
           _ (eq_sym (cf_cont f c))).
Qed.

Lemma sup_fixp_prefixed (fs : chain [D →c D]) :
  (⊔ fs) (⊔ (fixp_chain fs)) ⊑ ⊔ (fixp_chain fs).
Proof.
  set (y := ⊔ (fixp_chain fs)).
  (* Step 1: decompose (⊔ fs) y = ⊔_n (fs.[n] y) via bridge *)
  apply fun_sup_app_le; intros n.
  (* Goal: fs.[n] y ⊑ y *)
  (* Step 2: decompose fs.[n] y = ⊔_m fs.[n] (fixp (fs.[m])) via bridge *)
  apply cf_app_sup_le; intros m.
  (* Goal: fs.[n] (fixp (fs.[m])) ⊑ y *)
  (* Step 3: bound by fixp (fs.[max n m]) *)
  set (p := Nat.max n m).
  apply @le_trans with (y := fixp (fs.[p])).
  - (* fs.[n] (fixp (fs.[m])) ⊑ fixp (fs.[p]) *)
    (* = fs.[p] (fixp (fs.[p]))  by fixp_is_fixedpoint *)
    rewrite <- (fixp_is_fixedpoint (fs.[p])).
    apply @le_trans with (y := fs.[p] (fixp (fs.[m]))).
    + (* fs.[n] ⊑ fs.[p] pointwise, since n ≤ p *)
      exact (ch_mono fs n p (Nat.le_max_l n m)
               (fixp (fs.[m]))).
    + (* fixp (fs.[m]) ⊑ fixp (fs.[p]) by fixp_mono, since m ≤ p *)
      apply (mf_mono (cf_mono (fs.[p]))).
      exact (fixp_mono _ _ (fun x => ch_mono fs m p (Nat.le_max_r n m) x)).
  - (* fixp (fs.[p]) ⊑ y by sup_upper *)
    exact (sup_upper (fixp_chain fs) p).
Qed.

(*
    [fixp] is Scott-continuous on the function-space CPO.

    Proof: by [continuous_of_le], it suffices to show the ⊑ direction:
      [fixp (⊔ fs) ⊑ ⊔ₙ fixp (fs.[n])].

    Since [⊔ₙ fixp (fs.[n])] is a pre-fixed-point of [⊔ fs]
    (by [sup_fixp_prefixed]), [fixp_least] gives the result.
*)
Lemma fixp_continuous : continuous fixp_mono_fun.
Proof.
  apply continuous_of_le; intros fs.
  simpl. apply fixp_least.
  exact (sup_fixp_prefixed fs).
Qed.

(*
    The continuous fixed-point operator:

        FIXP : [[D →c D] →c D]

    [FIXP f = fixp f = ⊔ₙ fⁿ(⊥)] for any [f : [D →c D]].
*)
Definition FIXP : [[D →c D] →c D] :=
  Build_cont_fun fixp_mono_fun fixp_continuous.

(*  Computation rule: [FIXP f = fixp f]. *)
Lemma FIXP_eq (f : [D →c D]) : FIXP f = fixp f.
Proof. reflexivity. Qed.

(*  [FIXP f] is a fixed point of [f]. *)
Lemma FIXP_is_fixedpoint (f : [D →c D]) : f (FIXP f) = FIXP f.
Proof. exact (fixp_is_fixedpoint f). Qed.

(*  [FIXP f] is the least fixed point of [f]. *)
Lemma FIXP_least (f : [D →c D]) (x : D) : f x ⊑ x -> FIXP f ⊑ x.
Proof. exact (fixp_least f x). Qed.

(*  [FIXP f] is the least pre-fixed point of [f]. *)
Lemma FIXP_least_fixedpoint (f : [D →c D]) (x : D) : f x = x -> FIXP f ⊑ x.
Proof. intro H; apply FIXP_least; rewrite H; apply le_refl. Qed.

(*  Fixed-point induction via [FIXP]. *)
Lemma FIXP_ind (f : [D →c D]) (P : D -> Prop) :
    admissible P -> P ⊥ -> (forall x, P x -> P (f x)) -> P (FIXP f).
Proof. exact (fixp_ind f P). Qed.

End FIXP.