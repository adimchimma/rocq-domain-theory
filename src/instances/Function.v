(*  Function Instance — CPO Is Self-Enriched + Function-Space Utilities

    This is [src/instances/Function.v].

    Primary deliverable (§1):
      Register [CPO.type] as a [CPOEnrichedCat] — i.e. prove that the
      category of CPOs and continuous maps is enriched over itself.  The
      hom-objects are the function-space CPOs [[D →c E]] with the
      pointwise order; composition is [cont_comp]; identity is [cont_id].
      The separate Scott-continuity conditions (DD-002) are provided by
      [postcomp_continuous] and [precomp_continuous], proved in §5.

    Secondary deliverables (§2–§6):
      Convenience continuous maps used by [PCF_Denotational.v] and
      [EnrichedTheory.v]:

        §2  [cont_const e] — constant function [fun _ => e]; K combinator
        §3  [cont_ap x]    — evaluation at a point [f ↦ f x]
        §4  [cont_precomp g] — pre-composition [f ↦ f ∘ g]
        §5  [cont_postcomp g] — post-composition [f ↦ g ∘ f]
        §6  [cont_flip f]  — argument-flip of a curried function

    Imports:
      [src/structures/Order.v]       — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]         — CPO, PointedCPO, continuous
      [src/structures/Morphisms.v]   — cont_fun, cont_comp, cont_id,
                                       cont_comp_id_l, cont_comp_id_r,
                                       cont_comp_assoc
      [src/structures/Enriched.v]    — HasHom, HasId, IsCPOEnriched,
                                       CPOEnrichedCat
      [src/theory/OrderTheory.v]     — mono_fun_ext
      [src/theory/CPOTheory.v]       — cont_fun_ext, continuous_of_le,
                                       sup_ext
      [src/theory/FunctionSpaces.v]  — HB CPO instances on [D →c E],
                                       eval_at_mono, pointwise_chain,
                                       fun_sup_apply, sup_apply,
                                       postcomp_mono_fun (via §5 below)

    Phase coverage:
      Phase 0 — §2, §3
      Phase 1 — §1 (CPOEnrichedCat), §4, §5, §6
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Theory Require Import OrderTheory CPOTheory FunctionSpaces.


(* ================================================================== *)
(*   §1  CPO.type is a CPO-enriched category                         *)
(* ================================================================== *)
(*
    The category CPO, with objects [CPO.type], hom-CPOs [[D →c E]]
    (pointwise order, from [FunctionSpaces.v]), identity [cont_id],
    and composition [cont_comp], is a [CPOEnrichedCat].

    This is the canonical example of a CPO-enriched category
    (Abramsky & Jung §5.2.2).

    The enrichment axioms reduce to:
      comp_mono_l f   — post-composition with [f] is monotone
                        (proved as [postcomp_mono] in §5)
      comp_mono_r g   — pre-composition with [g] is monotone
                        (proved as [precomp_mono] in §4)
      comp_cont_l f   — post-composition with [f] is Scott-continuous
                        (proved as [postcomp_continuous] in §5)
      comp_cont_r g   — pre-composition with [g] is Scott-continuous
                        (proved as [precomp_continuous] in §4)

    Note on field ordering in [IsCPOEnriched.Build]:
      HB requires monotonicity witnesses before continuity witnesses,
      because the [continuous] predicate takes a [mono_fun] as argument.
      The fields appear in the order: comp, mono_l, mono_r, cont_l,
      cont_r, id_l, id_r, assoc.

    Note on [comp_assoc] direction:
      [IsCPOEnriched] requires [(h ∘ g) ∘ f = h ∘ (g ∘ f)].
      [cont_comp_assoc] from [Morphisms.v] proves the reverse,
      [h ∘ (g ∘ f) = (h ∘ g) ∘ f], so we take [eq_sym].

    Design note: separate continuity (DD-002) avoids a dependency on
    [Products.v] inside [Enriched.v].  The separate conditions are
    equivalent to joint continuity by A&J Lemma 3.2.6.
*)

(*
    §5 (post-composition) and §4 (pre-composition) provide the
    monotonicity and continuity lemmas needed below.  They are stated
    before the HB instance declaration and referenced by name.
*)


(* --- Post-composition monotonicity and continuity --- *)

Section PostComp.
Context {C D E : CPO.type}.

Definition postcomp_fun (g : [D →c E]) (f : [C →c D]) : [C →c E] :=
  cont_comp g f.

Lemma postcomp_mono (g : [D →c E]) :
  forall (f1 f2 : [C →c D]), fun_le f1 f2 ->
    fun_le (postcomp_fun g f1) (postcomp_fun g f2).
Proof.
  intros f1 f2 Hf c.
  unfold postcomp_fun; simpl.
  apply (mf_mono (cf_mono g)).
  exact (Hf c).
Qed.

Definition postcomp_mono_fun (g : [D →c E]) : mono_fun ([C →c D]) ([C →c E]) :=
  Build_mono_fun (postcomp_fun g) (postcomp_mono g).

(*
    Post-composition with [g] is Scott-continuous.

    For a chain [fs] of functions [C →c D] and a point [c : C]:
      (g ∘ ⊔ fs)(c) = g((⊔ fs)(c))
                     = g(⊔_n fs.[n] c)      [fun_sup_apply]
                     = ⊔_n g(fs.[n] c)      [continuity of g]
                     = ⊔_n (g ∘ fs.[n])(c)
                     = (⊔ (map_chain (g ∘ -) fs))(c)

    Both equalities use pointwise sup; the proof applies [cont_fun_ext]
    to reduce to a point, then rewrites via [cf_cont g] and [sup_ext].
*)
Lemma postcomp_continuous (g : [D →c E]) :
  continuous (postcomp_mono_fun g).
Proof.
  intro fs.
  apply cont_fun_ext; intro c. simpl.
  unfold fun_sup_fun. simpl.
  (* Goal: g (⊔ pointwise_chain fs c) = ⊔ pointwise_chain (map_chain ...) c *)
  rewrite (cf_cont g (pointwise_chain fs c)).
  apply sup_ext. intro n. simpl.
  reflexivity.
Qed.

Definition cont_postcomp (g : [D →c E]) : [([C →c D]) →c ([C →c E])] :=
  Build_cont_fun (postcomp_mono_fun g) (postcomp_continuous g).

Lemma cont_postcomp_apply (g : [D →c E]) (f : [C →c D]) (c : C) :
  cont_postcomp g f c = g (f c).
Proof.
  reflexivity.
Qed.

End PostComp.


(* --- Pre-composition monotonicity and continuity --- *)

Section PreComp.
Context {C D E : CPO.type}.

Definition precomp_fun (g : [C →c D]) (f : [D →c E]) : [C →c E] :=
  cont_comp f g.

Lemma precomp_mono (g : [C →c D]) :
  forall (f1 f2 : [D →c E]), fun_le f1 f2 ->
    fun_le (precomp_fun g f1) (precomp_fun g f2).
Proof.
  intros f1 f2 Hf c.
  unfold precomp_fun; simpl.
  exact (Hf (g c)).
Qed.

Definition precomp_mono_fun (g : [C →c D]) : mono_fun ([D →c E]) ([C →c E]) :=
  Build_mono_fun (precomp_fun g) (precomp_mono g).

(*
    Pre-composition with [g] is Scott-continuous.

    For a chain [fs] of functions [D →c E] and a point [c : C]:
      ((⊔ fs) ∘ g)(c) = (⊔ fs)(g c)
                       = ⊔_n (fs.[n] (g c))   [sup_apply]
                       = ⊔_n (fs.[n] ∘ g)(c)

    All equalities are definitional after [sup_apply]; [reflexivity] closes
    each goal.
*)
Lemma precomp_continuous (g : [C →c D]) :
  continuous (precomp_mono_fun g).
Proof.
  intro fs.
  apply cont_fun_ext; intro c. simpl.
  unfold fun_sup_fun. simpl.
  apply sup_ext. intro n. simpl.
  reflexivity.
Qed.

Definition cont_precomp (g : [C →c D]) : [([D →c E]) →c ([C →c E])] :=
  Build_cont_fun (precomp_mono_fun g) (precomp_continuous g).

Lemma cont_precomp_apply (g : [C →c D]) (f : [D →c E]) (c : C) :
  cont_precomp g f c = f (g c).
Proof.
  reflexivity.
Qed.

End PreComp.


(*
    Now that [postcomp_mono], [postcomp_continuous], [precomp_mono], and
    [precomp_continuous] are in scope, we can register the three HB
    instances that make [CPO.type] a [CPOEnrichedCat].
*)

HB.instance Definition CPO_HasHom :=
  HasHom.Build CPO.type (fun D E => [D →c E]).

HB.instance Definition CPO_HasId :=
  HasId.Build CPO.type (fun A => cont_id A).

(*
    [IsCPOEnriched.Build] field correspondence:
      comp        ↦  cont_comp
      comp_mono_l ↦  postcomp_mono   (g fixed, vary the input)
      comp_mono_r ↦  precomp_mono    (g fixed, vary the function)
      comp_cont_l ↦  postcomp_continuous
      comp_cont_r ↦  precomp_continuous
      comp_id_l   ↦  cont_comp_id_l
      comp_id_r   ↦  cont_comp_id_r
      comp_assoc  ↦  eq_sym (cont_comp_assoc ...)
                     (direction: mixin needs (h∘g)∘f = h∘(g∘f);
                      cont_comp_assoc proves h∘(g∘f) = (h∘g)∘f)
*)
HB.instance Definition CPO_IsCPOEnriched :=
  IsCPOEnriched.Build CPO.type
    (*  comp          *)  (fun A B C f g   => cont_comp f g)
    (*  comp_mono_l   *)  (fun A B C f     => postcomp_mono f)
    (*  comp_mono_r   *)  (fun A B C g     => precomp_mono g)
    (*  comp_cont_l   *)  (fun A B C f     => postcomp_continuous f)
    (*  comp_cont_r   *)  (fun A B C g     => precomp_continuous g)
    (*  comp_id_l     *)  (fun A B f       => cont_comp_id_l f)
    (*  comp_id_r     *)  (fun A B f       => cont_comp_id_r f)
    (*  comp_assoc    *)  (fun A B C D h g f => eq_sym (cont_comp_assoc h g f)).


(* ================================================================== *)
(*   §2  Constant continuous function                                 *)
(* ================================================================== *)
(*
    [cont_const e : [D →c E]] is the constant function [fun _ => e].
    This is the analogue of the K combinator.

    [cont_K : [E →c ([D →c E])]] is [e ↦ cont_const e],
    the curried form.  Continuity of [cont_K] follows because
    [cont_const (⊔ c)] applied at any point [d] equals [⊔ c],
    which is the sup of the chain [n ↦ cont_const (c.[n]) d = c.[n]].
*)

Section ConstFun.
Context {D E : CPO.type}.

Definition const_mono (e : E) : mono_fun D E :=
  Build_mono_fun (fun _ => e) (fun _ _ _ => le_refl e).

Lemma const_continuous (e : E) : continuous (const_mono e).
Proof.
  apply continuous_of_le; intro c.
  exact (sup_upper (map_chain (const_mono e) c) 0).
Qed.

Definition cont_const (e : E) : [D →c E] :=
  Build_cont_fun (const_mono e) (const_continuous e).

Lemma cont_const_apply (e : E) (d : D) : cont_const e d = e.
Proof.
  reflexivity.
Qed.

(*  [e ↦ cont_const e] is monotone: if [e1 ⊑ e2] then for all [d],
    [(cont_const e1) d = e1 ⊑ e2 = (cont_const e2) d].  *)
Definition cont_K_mono_fun : mono_fun E ([D →c E]) :=
  Build_mono_fun cont_const (fun e1 e2 (He : e1 ⊑ e2) d => He).

(*  Continuity of [cont_K]: [cont_const (⊔ c) = ⊔ (map_chain cont_const c)]
    pointwise: both sides equal [⊔ c] when applied at any [d].           *)
Lemma cont_K_continuous : continuous cont_K_mono_fun.
Proof.
  intro c.
  apply cont_fun_ext; intro d.
  simpl.
  unfold fun_sup_fun.
  apply sup_ext; intro n.
  reflexivity.
Qed.

Definition cont_K : [E →c ([D →c E])] :=
  Build_cont_fun cont_K_mono_fun cont_K_continuous.

Lemma cont_K_apply (e : E) (d : D) : cont_K e d = e.
Proof.
  reflexivity.
Qed.

End ConstFun.


(* ================================================================== *)
(*   §3  Evaluation at a point                                        *)
(* ================================================================== *)
(*
    [cont_ap x : [([D →c E]) →c E]] is the map [f ↦ f x].
    This is the pointwise specialisation of the full evaluation map
    [cont_eval] from [FunctionSpaces.v].

    Continuity: [(⊔ fs) x = ⊔_n (fs.[n] x)] is exactly [sup_apply].
*)

Section ApplyAt.
Context {D E : CPO.type}.

Lemma eval_at_continuous (x : D) : continuous (eval_at_mono (D:=D) (E:=E) x).
Proof.
  intro fs.
  exact (sup_apply fs x).
Qed.

Definition cont_ap (x : D) : [([D →c E]) →c E] :=
  Build_cont_fun (eval_at_mono x) (eval_at_continuous x).

Lemma cont_ap_apply (x : D) (f : [D →c E]) : cont_ap x f = f x.
Proof.
  reflexivity.
Qed.

End ApplyAt.


(* ================================================================== *)
(*   §4  Pre-composition (already proved above for §1)               *)
(* ================================================================== *)
(*
    [cont_precomp g : [([D →c E]) →c ([C →c E])]] sends
    [f ↦ f ∘ g].  This is the contravariant functorial action of the
    function-space in its domain argument.

    The monotonicity and continuity proofs live in [PreComp] above.
    We just export the corollary here for documentation.
*)

(* cont_precomp, cont_precomp_apply already defined above. *)


(* ================================================================== *)
(*   §5  Post-composition (already proved above for §1)              *)
(* ================================================================== *)
(*
    [cont_postcomp g : [([C →c D]) →c ([C →c E])]] sends
    [f ↦ g ∘ f].  This is the covariant functorial action of the
    function-space in its codomain argument.

    The monotonicity and continuity proofs live in [PostComp] above.
*)

(* cont_postcomp, cont_postcomp_apply already defined above. *)


(* ================================================================== *)
(*   §6  Flip                                                         *)
(* ================================================================== *)
(*
    [cont_flip f : [B →c ([A →c C])]] swaps the two arguments
    of a curried continuous function [f : [A →c ([B →c C])]]:
        (cont_flip f) b a = f a b

    We build this in three steps, following the same pattern as
    [FunctionSpaces.v]'s curry construction.

    (i)   [flip_inner_mono f b] : monotone function [A → C], for fixed [b].
    (ii)  [flip_inner_cont f b] : [flip_inner_mono f b] is continuous.
    (iii) [flip_val f b] : packages (i)+(ii) as [[A →c C]].
    (iv)  [flip_val_mono f] : [b ↦ flip_val f b] is monotone.
    (v)   [flip_continuous f] : [b ↦ flip_val f b] is continuous.
    (vi)  [cont_flip f] : the final continuous function.
*)

Section Flip.
Context {A B C : CPO.type}.

(*  (i) The inner monotone function, fixing [b : B].  *)
Definition flip_inner_mono (f : [A →c ([B →c C])]) (b : B)
    : mono_fun A C :=
  Build_mono_fun
    (fun a => (f a : [B →c C]) b)
    (fun a1 a2 Ha =>
      (mf_mono (cf_mono f) a1 a2 Ha : fun_le (f a1) (f a2)) b).

(*  (ii) Continuity of the inner function.

    For a chain [ca : chain A]:
      (f (⊔ ca) : [B →c C]) b
        = (⊔ (map_chain (cf_mono f) ca) : [B →c C]) b
                                          [by cf_cont f]
        = ⊔_n ((f (ca.[n])) b)            [sup_apply]
        = ⊔ (map_chain (flip_inner_mono f b) ca)   *)
Lemma flip_inner_cont (f : [A →c ([B →c C])]) (b : B) :
  continuous (flip_inner_mono f b).
Proof.
  intro ca.
  simpl.
  rewrite (cf_cont f ca).
  apply sup_ext; intro n.
  reflexivity.
Qed.

(*  (iii) Package as cont_fun.  *)
Definition flip_val (f : [A →c ([B →c C])]) (b : B) : [A →c C] :=
  Build_cont_fun (flip_inner_mono f b) (flip_inner_cont f b).

(*  (iv) [b ↦ flip_val f b] is monotone.
    [b1 ⊑ b2] implies [f a b1 ⊑ f a b2] for all [a] (monotonicity of [f a]).  *)
Lemma flip_val_mono (f : [A →c ([B →c C])]) :
  forall (b1 b2 : B), b1 ⊑ b2 -> fun_le (flip_val f b1) (flip_val f b2).
Proof.
  intros b1 b2 Hb a; simpl.
  exact (mf_mono (cf_mono (f a : [B →c C])) b1 b2 Hb).
Qed.

Definition flip_mono_fun (f : [A →c ([B →c C])])
    : mono_fun B ([A →c C]) :=
  Build_mono_fun (flip_val f) (flip_val_mono f).

(*  (v) Continuity of [b ↦ flip_val f b].

    For a chain [cb : chain B] and fixed [a : A]:
      (flip_val f (⊔ cb)) a = (f a : [B →c C]) (⊔ cb)
        = ⊔_n ((f a) (cb.[n]))              [continuity of f a]
        = ⊔_n (flip_val f (cb.[n]) a)       [definition]
        = (⊔ (map_chain (flip_mono_fun f) cb)) a   *)
Lemma flip_continuous (f : [A →c ([B →c C])]) :
  continuous (flip_mono_fun f).
Proof.
  intro cb.
  apply cont_fun_ext; intro a.
  simpl.
  rewrite (cf_cont (f a : [B →c C]) cb).
  apply sup_ext; intro n.
  reflexivity.
Qed.

Definition cont_flip (f : [A →c ([B →c C])]) : [B →c ([A →c C])] :=
  Build_cont_fun (flip_mono_fun f) (flip_continuous f).

Lemma cont_flip_apply (f : [A →c ([B →c C])]) (a : A) (b : B) :
  cont_flip f b a = (f a : [B →c C]) b.
Proof.
  reflexivity.
Qed.

End Flip.

(*  Flip is involutive: [cont_flip (cont_flip f) = f].  *)
Lemma cont_flip_involutive {A B C : CPO.type} (f : [A →c ([B →c C])]) :
  cont_flip (cont_flip f) = f.
Proof.
  apply cont_fun_ext; intro a.
  apply cont_fun_ext; intro b.
  reflexivity.
Qed.