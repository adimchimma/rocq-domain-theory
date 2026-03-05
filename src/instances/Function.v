(*  Function Instance — Continuous Function Space

    Convenience re-export and additional utility lemmas for the
    continuous-function-space CPO.

    The HB instances registering [cont_fun D E] as a [CPO.type]
    (and [PointedCPO.type] when [E] is pointed) live in
    [src/theory/FunctionSpaces.v].  This file provides:

    §1  Notation: [D →c E] for [cont_fun D E].
    §2  Constant continuous function [cont_const].
    §3  Application map [cont_ap x] : continuous map [f ↦ f x].
    §4  Pre-composition [cont_precomp g] : continuous map [f ↦ f ∘ g].
    §5  Post-composition [cont_postcomp g] : continuous map [f ↦ g ∘ f].
    §6  Flip: [cont_flip f] swaps arguments of a curried continuous function.

    This is [src/instances/Function.v].

    Imports:
      [src/structures/Order.v]       — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]         — CPO, PointedCPO, continuous
      [src/structures/Morphisms.v]   — cont_fun, cont_comp, cont_id
      [src/theory/OrderTheory.v]     — mono_fun_ext
      [src/theory/CPOTheory.v]       — cont_fun_ext, continuous_of_le
      [src/theory/FunctionSpaces.v]  — HB instances, eval, curry, uncurry,
                                       pointwise_chain, fun_sup_apply,
                                       eval_at_mono

    Phase coverage:
      Phase 0 — all sections
      Phase 1 — used in [PCF_Denotational.v], [EnrichedTheory.v]
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory CPOTheory FunctionSpaces.

From Stdlib Require Import ProofIrrelevance.


(* ================================================================== *)
(*   §1  Notation                                                      *)
(* ================================================================== *)

Declare Scope fun_cpo_scope.
Delimit Scope fun_cpo_scope with cpo_fun.

Notation "[ D →c E ]" := (cont_fun D E)
  (at level 0, D at level 99, E at level 200, no associativity)
  : fun_cpo_scope.

Open Scope fun_cpo_scope.


(* ================================================================== *)
(*   §2  Constant continuous function                                 *)
(* =============================================================== *)
(*
    For any [e : E], the constant function [fun _ => e] is continuous.
    This is the analogue of [K] in combinatory logic.
*)

Section ConstFun.
Context {D E : CPO.type}.

Definition const_mono (e : E) : mono_fun D E :=
  Build_mono_fun (fun _ => e) (fun _ _ _ => le_refl e).

Lemma const_continuous (e : E) : continuous (const_mono e).
Proof.
  apply continuous_of_le.
  intro c.
  apply (sup_upper (map_chain (const_mono e) c) 0).
Qed.

Definition cont_const (e : E) : [D →c E] :=
  Build_cont_fun (const_mono e) (const_continuous e).

Lemma cont_const_apply (e : E) (d : D) : cont_const e d = e.
Proof. 
  reflexivity. 
Qed.

(*
    The map [e ↦ cont_const e] is itself continuous as a function
    [E →c [D →c E]].  This is the "curried constant" or "K combinator".
*)
Definition cont_const_mono_fun : mono_fun E [D →c E] :=
  Build_mono_fun cont_const
    (fun (e1 e2 : E) (He : e1 ⊑ e2) (d : D) => He).

Lemma cont_const_continuous : continuous cont_const_mono_fun.
Proof.
  intro c.
  apply cont_fun_ext; intro d. simpl.
  unfold fun_sup_fun.
  apply sup_ext. intro n. simpl.
  reflexivity.
Qed.

Definition cont_K : [E →c [D →c E]] :=
  Build_cont_fun cont_const_mono_fun cont_const_continuous.

Lemma cont_K_apply (e : E) (d : D) : cont_K e d = e.
Proof. 
  reflexivity. 
Qed.

End ConstFun.


(* ================================================================== *)
(*   §3  Application map                                               *)
(* ================================================================== *)
(*
    For a fixed [x : D], the map [f ↦ f x] from [[D →c E]] to [E]
    is continuous (evaluation at a point).  This is the "pointwise
    evaluation" special case of the full [cont_eval].  It wraps
    [eval_at_mono] from FunctionSpaces.v.
*)

Section ApplyAt.
Context {D E : CPO.type}.

Lemma eval_at_continuous (x : D) : continuous (eval_at_mono (D:=D) (E:=E) x).
Proof.
  intro fs.
  exact (sup_apply fs x).
Qed.

Definition cont_ap (x : D) : [[D →c E] →c E] :=
  Build_cont_fun (eval_at_mono x) (eval_at_continuous x).

Lemma cont_ap_apply (x : D) (f : [D →c E]) : cont_ap x f = f x.
Proof. 
  reflexivity. 
Qed.

End ApplyAt.


(* ================================================================== *)
(*   §4  Pre-composition                                               *)
(* ================================================================== *)
(*
    Given [g : C →c D], pre-composition [f ↦ f ∘ g] is a continuous
    map [[D →c E] →c [C →c E]].  This is the contravariant action
    of the function-space functor in the first argument.
*)

Section PreComp.
Context {C D E : CPO.type}.

Definition precomp_fun (g : [C →c D]) (f : [D →c E]) : [C →c E] :=
  cont_comp f g.

Lemma precomp_mono (g : [C →c D]) :
  forall (f1 f2 : [D →c E]), fun_le f1 f2 -> fun_le (precomp_fun g f1) (precomp_fun g f2).
Proof.
  intros f1 f2 Hf c. unfold precomp_fun. simpl.
  exact (Hf (g c)).
Qed.

Definition precomp_mono_fun (g : [C →c D]) : mono_fun [D →c E] [C →c E] :=
  Build_mono_fun (precomp_fun g) (precomp_mono g).

Lemma precomp_continuous (g : [C →c D]) :
  continuous (precomp_mono_fun g).
Proof.
  intro fs.
  apply cont_fun_ext; intro c. simpl.
  unfold fun_sup_fun. simpl.
  apply sup_ext. intro n. simpl.
  reflexivity.
Qed.

Definition cont_precomp (g : [C →c D]) : [[D →c E] →c [C →c E]] :=
  Build_cont_fun (precomp_mono_fun g) (precomp_continuous g).

Lemma cont_precomp_apply (g : [C →c D]) (f : [D →c E]) (c : C) :
  cont_precomp g f c = f (g c).
Proof. reflexivity. Qed.

End PreComp.


(* ================================================================== *)
(*   §5  Post-composition                                              *)
(* ================================================================== *)
(*
    Given [g : D →c E], post-composition [f ↦ g ∘ f] is a continuous
    map [[C →c D] →c [C →c E]].  This is the covariant action of
    the function-space functor in the second argument.
*)

Section PostComp.
Context {C D E : CPO.type}.

Definition postcomp_fun (g : [D →c E]) (f : [C →c D]) : [C →c E] :=
  cont_comp g f.

Lemma postcomp_mono (g : [D →c E]) :
  forall (f1 f2 : [C →c D]), fun_le f1 f2 -> fun_le (postcomp_fun g f1) (postcomp_fun g f2).
Proof.
  intros f1 f2 Hf c. unfold postcomp_fun. simpl.
  apply (mf_mono (cf_mono g)).
  exact (Hf c).
Qed.

Definition postcomp_mono_fun (g : [D →c E]) : mono_fun [C →c D] [C →c E] :=
  Build_mono_fun (postcomp_fun g) (postcomp_mono g).

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

Definition cont_postcomp (g : [D →c E]) : [[C →c D] →c [C →c E]] :=
  Build_cont_fun (postcomp_mono_fun g) (postcomp_continuous g).

Lemma cont_postcomp_apply (g : [D →c E]) (f : [C →c D]) (c : C) :
  cont_postcomp g f c = g (f c).
Proof. 
  reflexivity. 
Qed.

End PostComp.


(* ================================================================== *)
(*   §6  Flip                                                          *)
(* ================================================================== *)
(*
    Given [f : A →c [B →c C]], produce [flip f : B →c [A →c C]].
    This is [flip f b a = f a b], shown continuous in both arguments.
*)

Section Flip.
Context {A B C : CPO.type}.

Definition flip_inner_mono (f : [A →c [B →c C]]) (b : B) : mono_fun A C.
Proof.
  refine (Build_mono_fun (fun (a : A) => (f a : cont_fun B C) b) _).
  intros a1 a2 Ha.
  exact ((mf_mono (cf_mono f) a1 a2 Ha : fun_le (f a1) (f a2)) b).
Defined.

Lemma flip_inner_cont (f : [A →c [B →c C]]) (b : B) :
  continuous (flip_inner_mono f b).
Proof.
  intro ca.
  simpl.
  (* Goal: (f (⊔ ca) : cont_fun B C) b = ⊔ (map_chain (flip_inner_mono f b) ca) *)
  (* Step 1: rewrite f (⊔ ca) via continuity of f *)
  assert (Hf : f (⊔ ca) = ⊔ (map_chain (cf_mono f) ca)).
  { exact (cf_cont f ca). }
  rewrite Hf.
  (* Now LHS: (⊔ (map_chain (cf_mono f) ca) : cont_fun B C) b *)
  (* This is fun_sup_fun (map_chain (cf_mono f) ca) b = ⊔ pointwise ... *)
  reflexivity.
Qed.

Definition flip_val (f : [A →c [B →c C]]) (b : B) : [A →c C] :=
  Build_cont_fun (flip_inner_mono f b) (flip_inner_cont f b).

Lemma flip_val_mono (f : [A →c [B →c C]]) :
  forall (b1 b2 : B), b1 ⊑ b2 -> fun_le (flip_val f b1) (flip_val f b2).
Proof.
  intros b1 b2 Hb a. simpl.
  apply (mf_mono (cf_mono (f a : cont_fun B C))).
  exact Hb.
Qed.

Definition flip_mono_fun (f : [A →c [B →c C]]) : mono_fun B [A →c C] :=
  Build_mono_fun (flip_val f) (flip_val_mono f).

Lemma flip_continuous (f : [A →c [B →c C]]) :
  continuous (flip_mono_fun f).
Proof.
  intro cb.
  apply cont_fun_ext; intro a. simpl.
  unfold fun_sup_fun. simpl.
  rewrite (cf_cont (f a : cont_fun B C) cb).
  apply sup_ext. intro n. simpl.
  reflexivity.
Qed.

Definition cont_flip (f : [A →c [B →c C]]) : [B →c [A →c C]] :=
  Build_cont_fun (flip_mono_fun f) (flip_continuous f).

Lemma cont_flip_apply (f : [A →c [B →c C]]) (a : A) (b : B) :
  cont_flip f b a = (f a : cont_fun B C) b.
Proof. reflexivity. Qed.

End Flip.

(* Flip is involutive: [flip (flip f) = f]. *)
Lemma cont_flip_flip {A B C : CPO.type} (f : cont_fun A (cont_fun B C)) :
  cont_flip (cont_flip f) = f.
Proof.
  apply cont_fun_ext; intro a.
  apply cont_fun_ext; intro b.
  reflexivity.
Qed.

Close Scope fun_cpo_scope.
