(*  PCF_Denotational

    Phase 1: Denotational semantics for typed call-by-value PCF (PCFv).

    This is [src/lang/PCF_Denotational.v].

    Imports:
      [src/lang/PCF_Syntax.v]         — intrinsically typed syntax, renamings,
                                        substitutions, var_case
      [src/structures/Order.v]        — chains and monotone maps
      [src/structures/CPO.v]          — CPO.type, PointedCPO.type
      [src/structures/Morphisms.v]    — cont_fun, cont_comp, cont_id
      [src/theory/Lift.v]             — lifted CPO [option D], [ret], [kleisli]
      [src/theory/Products.v]         — product CPOs, π₁, π₂, cont_pair,
                                        cont_prod_map, cont_swap,
                                        prod_sup_fst, prod_sup_snd
      [src/theory/FunctionSpaces.v]   — continuous function-space CPO,
                                        cont_curry, cont_eval, FIXP
      [src/theory/FixedPoints.v]      — fixp, fixp_is_fixedpoint,
                                        FIXP_is_fixedpoint
      [src/theory/OrderTheory.v]      — le_antisym, le_trans
      [src/theory/ChainTheory.v]      — chain_shift, sup_shift,
                                        chain_some_stable
      [src/theory/CPOTheory.v]        — sup_upper, sup_least, sup_ext,
                                        cont_fun_ext
      [src/instances/Discrete.v]      — unit PointedCPO, bool CPO, nat CPO;
                                        nat_sup_eq, bool_sup_eq,
                                        nat_chain_const, bool_chain_const
      [src/instances/Function.v]      — cont_const, cont_flip, cont_ap

    Summary
    =======
    We give the denotational semantics for typed call-by-value PCF,
    following Benton, Kennedy, and Varming, "Some Domain Theory and
    Denotational Semantics in Coq", §3.  The lift monad [D⊥ = option D]
    carries partiality; [None] denotes divergence.

    Type interpretation:
        sem_ty Nat          = nat          (discrete CPO — Discrete.v §4)
        sem_ty Bool         = bool         (discrete CPO — Discrete.v §3)
        sem_ty (τ₁ →ₜ τ₂)  = [sem_ty τ₁ →c option (sem_ty τ₂)]
        sem_ty (τ₁ ×ₜ τ₂)  = sem_ty τ₁ * sem_ty τ₂

    Environment interpretation:
        sem_env []          = unit         (trivial PointedCPO — Discrete.v §1)
        sem_env (τ :: Γ)    = sem_ty τ * sem_env Γ

    Denotation:
        sem_val : Value Γ τ  →  [sem_env Γ →c sem_ty τ]
        sem_exp : Exp   Γ τ  →  [sem_env Γ →c option (sem_ty τ)]

    using a mutual structural fixpoint, with each case expressed as a
    point-free composition of library combinators.

    The development is structured in nine conceptual layers:

      §1  Type and environment interpretation into CPO domains
      §2  Variable denotation as iterated projection
      §3  Parameterised Kleisli lifting and arithmetic/branch combinators
      §4  Value and expression denotation (mutual fixpoint)
      §5  Closed-term semantics and notation
      §6  Semantic substitutions and their equations
      §7  Computation rules (β-rules)
      §8  Semantic renaming and weakening
      §9  Substitution extension, substitution lemmas, and corollaries

    Design note: because [Products.v] and [Lift.v] define conflicting
    angle-bracket notations, we write [option D] instead of [⟨D⟩⊥]
    throughout this file.

    Phase coverage:
      Phase 1 — all sections.
      Used by [PCF_Soundness.v] and [PCF_Adequacy.v].

    References:
      Benton, Kennedy, and Varming, "Some Domain Theory and Denotational
      Semantics in Coq", §3.
      Abramsky & Jung (1994) §2.1, §3.
*)

From HB Require Import structures.
From Stdlib Require Import List PeanoNat.
From Stdlib Require Import ClassicalEpsilon.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import
  Lift Products FunctionSpaces FixedPoints
  OrderTheory ChainTheory CPOTheory.
From DomainTheory.Instances Require Import Discrete Function.
From DomainTheory.Lang Require Import PCF_Syntax.

Import ListNotations.

(* Notation workaround: the conflicting angle-bracket notations from
   [Lift.v] and [Products.v] prevent [<>] from parsing in certain
   contexts.  We open [type_scope] to restore [<>] as [not eq]. *)
Local Open Scope type_scope.


(* ================================================================== *)
(*   §1  Type and environment interpretation                          *)
(* ================================================================== *)
(*
    [nat], [bool], and [unit] carry their discrete / trivial CPO
    structures from [Discrete.v §1–§4].

    The arrow type [τ₁ →ₜ τ₂] is interpreted as Scott-continuous maps
    into the LIFT of the codomain:
        [sem_ty τ₁ →c option (sem_ty τ₂)]
    The [option] layer models call-by-value partiality.  Since
    [option (sem_ty τ₂)] is a PointedCPO (Lift.v), so is the entire
    function space — enabling [fixp] for the FIX case.

    The product type [τ₁ ×ₜ τ₂] is the categorical product CPO from
    Products.v.

    [sem_env Γ] is the n-ary product of the types in [Γ].  The empty
    context denotes [unit] (the terminal PointedCPO from Discrete.v §1).
*)

Fixpoint sem_ty (τ : Ty) : CPO.type :=
  match τ with
  | Nat         => nat
  | Bool        => bool
  | Arrow τ₁ τ₂ => cont_fun (sem_ty τ₁) (option (sem_ty τ₂))
  | Prod τ₁ τ₂  => (sem_ty τ₁ * sem_ty τ₂)%type
  end.

(*  The function-type domain is a PointedCPO (codomain is [option] hence
    pointed).  Used by the FIX case (§4) to instantiate [FIXP]. *)
Definition sem_arrow_pointed (τ₁ τ₂ : Ty) : PointedCPO.type :=
  cont_fun (sem_ty τ₁) (option (sem_ty τ₂)).

(*
    Semantic environments mirror the intrinsic syntax: the head of the
    typing context is the first component of the semantic product.
    The empty context denotes [unit] (the terminal PointedCPO).
*)
Fixpoint sem_env (Γ : Env) : CPO.type :=
  match Γ with
  | []      => unit
  | τ :: Γ' => (sem_ty τ * sem_env Γ')%type
  end.

Notation "γ ↾ τ" := (fst γ) (at level 20, only parsing).
Notation "γ ↓ Γ" := (snd γ) (at level 20, only parsing).


(* ================================================================== *)
(*   §2  Variable denotation                                          *)
(* ================================================================== *)
(*
    [sem_var x] is the continuous projection for the de Bruijn index [x]:

        ZVAR      ↦  π₁
        SVAR x'   ↦  sem_var x' ∘ π₂
*)

Fixpoint sem_var {Γ : Env} {τ : Ty} (x : Var Γ τ)
    : cont_fun (sem_env Γ) (sem_ty τ) :=
  match x with
  | ZVAR    => π₁
  | SVAR x' => cont_comp (sem_var x') π₂
  end.

Lemma sem_var_ZVAR {Γ : Env} {τ : Ty} (γ : sem_env (τ :: Γ)) :
    sem_var ZVAR γ = fst γ.
Proof. reflexivity. Qed.

Lemma sem_var_SVAR {Γ : Env} {τ τ' : Ty}
    (x : Var Γ τ) (γ : sem_env (τ' :: Γ)) :
    sem_var (SVAR x) γ = sem_var x (snd γ).
Proof. reflexivity. Qed.


(* ================================================================== *)
(*   §3  Combinators                                                  *)
(* ================================================================== *)
(*
    This section collects the auxiliary continuous maps needed for the
    point-free semantics.  Each combinator is packaged as a [cont_fun]
    by establishing monotonicity (from discrete-order rewriting) and
    continuity (from the constant-chain property of discrete types).

    §3a  Parameterised Kleisli lifting (kleislir)
    §3b  Arithmetic binary operators (nat_binop)
    §3c  Comparison (nat_ltb_pair)
    §3d  Conditional (cont_ifb)
*)


(* ------------------------------------------------------------------ *)
(*   §3a  Parameterised Kleisli lifting                               *)
(* ------------------------------------------------------------------ *)
(*
    [kleislir f : [X × option Y →c option Z]]  for  [f : [X × Y →c option Z]].

    This is an "indexed Kleisli extension" that threads an extra parameter
    [x : X] through the lift monad.  It satisfies:

        kleislir f (x, None)   = None
        kleislir f (x, Some y) = f (x, y)

    and is jointly continuous in [x] and the lifted [option Y] argument.

    The continuity proof follows the same pattern as [continuous_kleisli]
    in [Lift.v]: case-split on whether the [option Y] component chain
    ever leaves [None], extract a stabilisation index [N] and a
    [D_chain] of [Y]-values, build a paired chain in [X × Y],
    apply [cf_cont f], and realign via [sup_shift] and [sup_ext].
*)

Section KleisliR.
Context {X Y Z : CPO.type}.

Definition kleislir_fun (f : cont_fun (X * Y)%type (option Z))
    (p : (X * option Y)%type) : option Z :=
  match snd p with None => None | Some e => f (fst p, e) end.

Lemma kleislir_mono (f : cont_fun (X * Y)%type (option Z))
    : monotone _ _ (kleislir_fun f).
Proof.
  intros [d1 me1] [d2 me2] [Hd Hme]; simpl in *.
  destruct me1 as [e1|], me2 as [e2|]; simpl; auto.
  - apply (mf_mono (cf_mono f)). split; simpl; auto.
  - exact (False_ind _ Hme).
Qed.

Definition kleislir_mfun (f : cont_fun (X * Y)%type (option Z))
    : mono_fun _ _ :=
  Build_mono_fun _ (kleislir_mono f).

Definition snd_chain (c : chain (X * option Y)%type)
    : chain (option Y) :=
  map_chain snd_mono c.

Definition paired_chain_fn (c : chain (X * option Y)%type)
    (N : nat) (y0 : Y)
    (HN : (snd_chain c).[N] <> None) (k : nat) : (X * Y)%type :=
  (fst (c.[N + k]), D_chain_fn N y0 (snd_chain c) k).

Lemma paired_chain_mono (c : chain (X * option Y)%type)
    (N : nat) (y0 : Y) (HN : (snd_chain c).[N] <> None) :
    forall m n, m <= n ->
    (paired_chain_fn c N y0 HN m) ⊑ (paired_chain_fn c N y0 HN n).
Proof.
  intros m n Hmn.
  split; simpl.
  - apply (mf_mono fst_mono).
    exact (ch_mono c _ _ (proj1 (Nat.add_le_mono_l m n N) Hmn)).
  - exact (D_chain_mono N y0 (snd_chain c) HN m n Hmn).
Qed.

Definition paired_chain (c : chain (X * option Y)%type)
    (N : nat) (y0 : Y)
    (HN : (snd_chain c).[N] <> None) : chain (X * Y)%type :=
  Build_chain _ (paired_chain_mono c N y0 HN).

(*
    Index-shift equality: the [N]-shifted image of [kleislir f] on [c]
    agrees pointwise with [f] applied to [paired_chain].
*)
Lemma kleislir_map_chain_shift_eq
    (f : cont_fun (X * Y)%type (option Z))
    (c : chain (X * option Y)%type)
    (N : nat) (y0 : Y) (HN : (snd_chain c).[N] <> None) (k : nat) :
    (map_chain (kleislir_mfun f) c).[N + k] =
    (map_chain (cf_mono f) (paired_chain c N y0 HN)).[k].
Proof.
  (* The proof is by case analysis on [snd (c.[N+k])].
     Both branches trivially reduce once the case is resolved.
     The [None] branch is contradicted by [chain_some_stable]. *)
  transitivity (
    match snd (c.[N + k]) with
    | Some e => f (fst (c.[N + k]), e)
    | None   => None
    end).
  { unfold map_chain; simpl. unfold kleislir_fun. reflexivity. }
  transitivity (
    mf_fun (cf_mono f)
           (fst (c.[N + k]),
            match snd (c.[N + k]) with
            | Some d => d
            | None   => y0
            end)).
  { destruct (snd (c.[N + k])) as [b|] eqn:Hsnd.
    - reflexivity.
    - exfalso.
      apply (chain_some_stable (map_chain snd_mono c) N k HN).
      unfold map_chain; simpl. exact Hsnd. }
  unfold map_chain, paired_chain, paired_chain_fn, D_chain_fn, snd_chain.
  simpl. reflexivity.
Qed.

(*
    The sup of [paired_chain] splits into the component sups, matching
    the original chain's structure.
*)
Lemma paired_chain_sup_eq (c : chain (X * option Y)%type)
    (N : nat) (y0 : Y) (HN : (snd_chain c).[N] <> None) :
    sup (paired_chain c N y0 HN) =
    (fst (sup c), sup (D_chain N y0 (snd_chain c) HN)).
Proof.
  apply injective_projections.
  - rewrite prod_sup_fst. simpl.
    transitivity (sup (chain_shift N (map_chain fst_mono c))).
    + apply sup_ext. intro k. simpl.
      rewrite Nat.add_comm. reflexivity.
    + rewrite sup_shift. exact (prod_sup_fst c).
  - rewrite prod_sup_snd. simpl.
    apply sup_ext. intro k. simpl. reflexivity.
Qed.

(*
    Continuity of [kleislir f].  The proof mirrors [continuous_kleisli]
    in [Lift.v].
*)
Lemma kleislir_continuous (f : cont_fun (X * Y)%type (option Z)) :
    continuous (kleislir_mfun f).
Proof.
  intros c.
  destruct (excluded_middle_informative
              (exists n, not ((snd_chain c).[n] = None))) as [Hex | Hall].
  - (* The [option Y] component eventually reaches [Some]. *)
    destruct (constructive_indefinite_description _ Hex) as [N HN].
    set (y0 := extract_some (snd_chain c).[N] HN).
    pose proof (lift_sup_some_eq (snd_chain c) N y0 HN) as Hsnd_sup.
    (* LHS: kleislir f (⊔ c) = f (fst(⊔c), ⊔ D_chain) *)
    assert (Hleft : kleislir_fun f (sup c) =
                    f (fst (sup c), sup (D_chain N y0 (snd_chain c) HN))).
    { unfold kleislir_fun.
      change (snd (sup c)) with (sup (snd_chain c)).
      rewrite Hsnd_sup. reflexivity. }
    (* f (fst(⊔c), ⊔ D_chain) = f (⊔ paired_chain) *)
    assert (Hleft2 :
      f (fst (sup c), sup (D_chain N y0 (snd_chain c) HN)) =
      f (sup (paired_chain c N y0 HN))).
    { f_equal. symmetry. exact (paired_chain_sup_eq c N y0 HN). }
    eapply eq_trans. { exact Hleft. }
    eapply eq_trans. { exact Hleft2. }
    eapply eq_trans.
    + (* Continuity of [f] *)
      exact (cf_cont f (paired_chain c N y0 HN)).
    + (* Reindex via [sup_shift] *)
      eapply eq_trans.
      * apply sup_ext; intro k.
        rewrite chain_shift_index.
        rewrite (Nat.add_comm k N).
        symmetry.
        exact (kleislir_map_chain_shift_eq f c N y0 HN k).
      * apply sup_shift.
  - (* The [option Y] component is always [None]. *)
    assert (HallEq : forall n, snd (c.[n]) = None).
    { intro n.
      destruct (snd (c.[n])) eqn:Hn; [|reflexivity].
      exfalso. apply Hall. exists n.
      change ((snd_chain c).[n] <> None).
      change (snd (c.[n]) <> None).
      rewrite Hn. discriminate. }
    pose proof (prod_sup_snd c) as Hsnd_eq.
    assert (Hsnd_none : sup (snd_chain c) = None).
    { apply lift_sup_none. intro n.
      unfold snd_chain, map_chain; simpl.
      exact (HallEq n). }
    assert (Hleft : kleislir_fun f (sup c) = None).
    { unfold kleislir_fun.
      change (snd (sup c)) with (sup (snd_chain c)).
      rewrite Hsnd_none. reflexivity. }
    assert (HallK :
      forall n, (map_chain (kleislir_mfun f) c).[n] = None).
    { intro n.
      change ((map_chain (kleislir_mfun f) c).[n]) with
        (kleislir_fun f (c.[n])).
      unfold kleislir_fun.
      destruct (c.[n]) as [xn [yn|]] eqn:Hcn; simpl.
      - exfalso. apply Hall. exists n.
        change ((snd_chain c).[n] <> None).
        change (snd (c.[n]) <> None).
        rewrite Hcn. simpl. discriminate.
      - reflexivity. }
    pose proof (lift_sup_none _ HallK) as Hright.
    eapply eq_trans. { exact Hleft. }
    exact (eq_sym Hright).
Qed.

Definition kleislir (f : cont_fun (X * Y)%type (option Z))
    : cont_fun (X * option Y)%type (option Z) :=
  Build_cont_fun _ (kleislir_continuous f).

Lemma kleislir_none (f : cont_fun (X * Y)%type (option Z)) (x : X) :
    kleislir f (x, None) = None.
Proof. reflexivity. Qed.

Lemma kleislir_some (f : cont_fun (X * Y)%type (option Z))
    (x : X) (y : Y) :
    kleislir f (x, Some y) = f (x, y).
Proof. reflexivity. Qed.

End KleisliR.


(* ------------------------------------------------------------------ *)
(*   §3b  Arithmetic binary operators (nat_binop)                     *)
(* ------------------------------------------------------------------ *)
(*
    Lifts [op : nat → nat → nat] to a continuous map [(nat × nat) →c nat].
    Monotonicity and continuity hold because [nat * nat] is a product of
    discrete CPOs, so every chain is constant componentwise.

    The proofs are factored out of [refine]/[Proof] mode because
    canonical-structure resolution for [nat * nat] prevents [destruct]
    on pair inhabitants when the goal still contains unresolved evars.
*)

Lemma nat_binop_mono (op : nat -> nat -> nat) :
    monotone (nat * nat)%type nat (fun p => op (fst p) (snd p)).
Proof.
  intros p q H.
  destruct p as [a1 b1], q as [a2 b2].
  apply prod_le_iff in H. destruct H as [Ha Hb].
  simpl in *. rewrite Ha, Hb. reflexivity.
Qed.

Definition nat_binop_mfun (op : nat -> nat -> nat)
    : mono_fun (nat * nat)%type nat :=
  Build_mono_fun _ (nat_binop_mono op).

Lemma nat_binop_cont (op : nat -> nat -> nat)
    : continuous (nat_binop_mfun op).
Proof.
  intro c.
  assert (Hsc : sup c = c.[0]).
  { apply le_antisym.
    - apply sup_least; intro n.
      pose proof (ch_mono c 0 n (Nat.le_0_l n)) as H0n.
      apply prod_le_iff in H0n. apply prod_le_iff.
      destruct H0n as [Ha Hb]. split; symmetry; assumption.
    - exact (sup_upper c 0). }
  rewrite Hsc. rewrite (nat_sup_eq (map_chain _ c)). reflexivity.
Qed.

Definition nat_binop (op : nat -> nat -> nat)
    : cont_fun (nat * nat)%type nat :=
  Build_cont_fun _ (nat_binop_cont op).


(* ------------------------------------------------------------------ *)
(*   §3c  Comparison (nat_ltb_pair)                                   *)
(* ------------------------------------------------------------------ *)
(*
    [nat_ltb_pair : [(nat × nat) →c bool]]   computes [snd <? fst] as a
    continuous map.  This matches the operational rule [e_Gt]:
    [GT n₁ n₂ ⇓ BLIT (n₂ <? n₁)].
*)

Lemma nat_ltb_pair_mono :
    monotone (nat * nat)%type bool
      (fun p => Nat.ltb (snd p) (fst p)).
Proof.
  intros p q H.
  destruct p as [a1 b1], q as [a2 b2].
  apply prod_le_iff in H. destruct H as [Ha Hb].
  simpl in *. rewrite Ha, Hb. reflexivity.
Qed.

Definition nat_ltb_pair_mfun : mono_fun (nat * nat)%type bool :=
  Build_mono_fun _ nat_ltb_pair_mono.

Lemma nat_ltb_pair_cont : continuous nat_ltb_pair_mfun.
Proof.
  intro c.
  assert (Hsc : sup c = c.[0]).
  { apply le_antisym.
    - apply sup_least; intro n.
      pose proof (ch_mono c 0 n (Nat.le_0_l n)) as H0n.
      apply prod_le_iff in H0n. apply prod_le_iff.
      destruct H0n as [Ha Hb]. split; symmetry; assumption.
    - exact (sup_upper c 0). }
  rewrite Hsc. rewrite (bool_sup_eq (map_chain _ c)). reflexivity.
Qed.

Definition nat_ltb_pair : cont_fun (nat * nat)%type bool :=
  Build_cont_fun _ nat_ltb_pair_cont.


(* ------------------------------------------------------------------ *)
(*   §3d  Conditional                                                 *)
(* ------------------------------------------------------------------ *)
(*
    [cont_ifb : [bool × (option D × option D) →c option D]]

    Given a boolean and two lifted branches, returns the first branch
    when [true] and the second when [false]:

        cont_ifb (true,  (e₁, e₂)) = e₁
        cont_ifb (false, (e₁, e₂)) = e₂

    Monotonicity projects the appropriate component's ordering.
    Continuity uses [bool_sup_eq] to observe that the boolean component
    is constant along the chain, then reduces to the sup of the
    chosen branch.
*)

Section CondSection.
Context {D : CPO.type}.

Definition ifb_fun (p : (bool * (option D * option D))%type) : option D :=
  if fst p then fst (snd p) else snd (snd p).

Lemma ifb_fun_eq (b : bool) (t f : option D) :
  ifb_fun (b, (t, f)) = if b then t else f.
Proof. reflexivity. Qed.

Lemma ifb_mono : monotone _ _ ifb_fun.
Proof.
  intros p q H.
  destruct p as [b1 [t1 f1]], q as [b2 [t2 f2]].
  apply prod_le_iff in H. destruct H as [Hb Hpair].
  apply prod_le_iff in Hpair. destruct Hpair as [Ht Hf].
  simpl in *. rewrite Hb. unfold ifb_fun; simpl.
  destruct b2; simpl; assumption.
Qed.

Lemma ifb_continuous : continuous (Build_mono_fun ifb_fun ifb_mono).
Proof.
  intro c.
  assert (Hbc : forall n, fst (c.[n]) = fst (c.[0])).
  { intro n.
    pose proof (ch_mono c 0 n (Nat.le_0_l n)) as H0n.
    apply prod_le_iff in H0n. destruct H0n as [Hb _].
    simpl in Hb. symmetry. exact Hb. }
  (* Factor the whole proof through explicit sups. *)
  assert (Hfst_sup : fst (sup c) = fst (c.[0])).
  { transitivity (sup (map_chain fst_mono c)).
    - reflexivity.
    - exact (bool_sup_eq (map_chain fst_mono c)). }
  destruct (fst (c.[0])) eqn:Hb.
  - (* true branch: ifb_fun picks fst ∘ snd *)
    transitivity (fst (snd (sup c))).
    + (* LHS: ifb_fun (sup c) = fst (snd (sup c)) *)
      destruct (sup c) as [bsup [tsup fsup]] eqn:Hsup.
      simpl in Hfst_sup. unfold ifb_fun. simpl.
      rewrite Hfst_sup. reflexivity.
    + simpl. change (fst (snd (sup c))) with
        (sup (map_chain (mono_fun_comp fst_mono snd_mono) c)).
      symmetry.
      apply sup_ext; intro n. simpl. unfold ifb_fun.
      destruct (fst c.[n]); rewrite Hbc; reflexivity.
  - (* false branch: ifb_fun picks snd ∘ snd *)
    transitivity (snd (snd (sup c))).
    + destruct (sup c) as [bsup [tsup fsup]] eqn:Hsup.
      simpl. simpl in Hfst_sup. rewrite Hfst_sup.
      unfold ifb_fun. simpl. reflexivity. 
    + simpl. change (snd (snd (sup c))) with
        (sup (map_chain (mono_fun_comp snd_mono snd_mono) c)).
      symmetry.
      apply sup_ext; intro n. simpl. unfold ifb_fun.
      destruct (fst c.[n]); rewrite Hbc; reflexivity.
Qed.

Definition cont_ifb
    : cont_fun (bool * (option D * option D))%type (option D) :=
  Build_cont_fun _ ifb_continuous.

End CondSection.


(* ================================================================== *)
(*   §4  Value and expression denotation                              *)
(* ================================================================== *)
(*
    The semantic maps [sem_val] and [sem_exp] are defined as a mutual
    structural fixpoint.  Each case is a point-free composition of
    library combinators.

    We follow the convoy pattern from [PCF_Syntax.v], matching on
    [Value G T] / [Exp G T] with generalised indices and a functionalised
    return type, to satisfy Coq's dependent-match requirements.

    Case glossary (values):
      VAR   x         : sem_var x
      NLIT  n         : cont_const n
      BLIT  b         : cont_const b
      PAIR  v₁ v₂    : cont_pair (sem_val v₁) (sem_val v₂)
      FIX  τ₁ τ₂ e   : FIXP ∘ flip(curry(flip(curry(sem_exp e))))

    Case glossary (expressions):
      VAL   v         : ret ∘ sem_val v
      APP   v₁ v₂    : eval ∘ ⟨sem_val v₁, sem_val v₂⟩
      FST   v         : ret ∘ π₁ ∘ sem_val v
      SND   v         : ret ∘ π₂ ∘ sem_val v
      LET   e₁ e₂    : kleislir(sem_exp e₂ ∘ swap) ∘ ⟨id, sem_exp e₁⟩
      OP    op v₁ v₂  : ret ∘ nat_binop op ∘ ⟨sem_val v₁, sem_val v₂⟩
      GT    v₁ v₂     : ret ∘ nat_ltb_pair ∘ ⟨sem_val v₁, sem_val v₂⟩
      IFB   v e₁ e₂   : cont_ifb ∘ ⟨sem_val v, ⟨sem_exp e₁, sem_exp e₂⟩⟩
*)

Fixpoint sem_val {Γ τ} (v : Value Γ τ) {struct v}
    : cont_fun (sem_env Γ) (sem_ty τ) :=
  match v in Value G T return cont_fun (sem_env G) (sem_ty T) with
  | VAR x =>
      sem_var x
  | NLIT n =>
      cont_const n
  | BLIT b =>
      cont_const b
  | PAIR v₁ v₂ =>
      cont_pair (sem_val v₁) (sem_val v₂)
  | FIX τ₁ τ₂ body =>
      cont_comp
        (@FIXP (sem_arrow_pointed τ₁ τ₂))
        (cont_flip (cont_curry (cont_flip (cont_curry (sem_exp body)))))
  end

with sem_exp {Γ τ} (e : Exp Γ τ) {struct e}
    : cont_fun (sem_env Γ) (option (sem_ty τ)) :=
  match e in Exp G T return cont_fun (sem_env G) (option (sem_ty T)) with
  | VAL v =>
      cont_comp ret (sem_val v)
  | APP v₁ v₂ =>
      cont_comp cont_eval (cont_pair (sem_val v₁) (sem_val v₂))
  | FST v =>
      cont_comp ret (cont_comp π₁ (sem_val v))
  | SND v =>
      cont_comp ret (cont_comp π₂ (sem_val v))
  | LET e₁ e₂ =>
      cont_comp
        (kleislir (cont_comp (sem_exp e₂) cont_swap))
        (cont_pair (cont_id _) (sem_exp e₁))
  | OP op v₁ v₂ =>
      cont_comp ret
        (cont_comp (nat_binop op) (cont_pair (sem_val v₁) (sem_val v₂)))
  | GT v₁ v₂ =>
      cont_comp ret
        (cont_comp nat_ltb_pair (cont_pair (sem_val v₁) (sem_val v₂)))
  | IFB v e₁ e₂ =>
      cont_comp cont_ifb
        (cont_pair (sem_val v) (cont_pair (sem_exp e₁) (sem_exp e₂)))
  end.


(* ================================================================== *)
(*   §5  Closed-term semantics and notation                           *)
(* ================================================================== *)
(*
    For closed terms the semantic environment is [tt : unit], so the
    denotation of a closed value/expression is the corresponding
    semantic map applied to [tt].

    The bracket notation [⟦ v ⟧ᵥ], [⟦ e ⟧ₑ] is introduced here and
    used throughout the remaining sections.
*)

Definition sem_cval {τ : Ty} (v : CValue τ) : sem_ty τ :=
  sem_val v tt.

Definition sem_cexp {τ : Ty} (e : CExp τ) : option (sem_ty τ) :=
  sem_exp e tt.

Notation "⟦ v ⟧ᵥ"  := (sem_val  v) (at level 9).
Notation "⟦ e ⟧ₑ"  := (sem_exp  e) (at level 9).
Notation "⟦ v ⟧ᶜᵥ" := (sem_cval v) (at level 9).
Notation "⟦ e ⟧ᶜₑ" := (sem_cexp e) (at level 9).


(* ================================================================== *)
(*   §6  Semantic substitutions and their equations                   *)
(* ================================================================== *)
(*
    Given a syntactic substitution [σ : Subst Γ Γ'], [sem_subst σ] is the
    continuous map from semantic environments for [Γ'] to semantic
    environments for [Γ].

    The key properties are:
      [sem_subst_var]:  lookup commutes with semantic substitution
      [sem_env_ext]:    extensionality principle for semantic environments
      [sem_subst_id]:   identity substitution acts as identity
*)

Fixpoint sem_subst {Γ Γ' : Env} (σ : Subst Γ Γ')
    : cont_fun (sem_env Γ') (sem_env Γ) :=
  match Γ as Δ return Subst Δ Γ' -> cont_fun (sem_env Γ') (sem_env Δ) with
  | [] => fun _ => cont_const tt
  | τ :: Δ =>
      fun σ' =>
        cont_pair
          (sem_val (σ' _ ZVAR))
          (sem_subst (fun τ0 x => σ' τ0 (SVAR x)))
  end σ.

Lemma sem_subst_var {Γ Γ' : Env} {τ : Ty}
    (σ : Subst Γ Γ') (x : Var Γ τ) (γ' : sem_env Γ') :
    sem_var x (sem_subst σ γ') = sem_val (σ _ x) γ'.
Proof.
  induction x as [| ? ? ? x IH]; simpl.
  - reflexivity.
  - exact (IH (fun τ0 y => σ τ0 (SVAR y))).
Qed.

(*
    Two semantic environments for [Γ] are equal when they agree on
    every variable projection.
*)
Lemma sem_env_ext {Γ : Env} (a b : sem_env Γ)
    (Hext : forall τ (x : Var Γ τ), sem_var x a = sem_var x b) :
    a = b.
Proof.
  induction Γ as [|σ Γ' IH].
  - destruct a, b. reflexivity.
  - apply injective_projections.
    + exact (Hext _ ZVAR).
    + apply IH. intros τ x. exact (Hext τ (SVAR x)).
Qed.

(*
    The identity substitution [fun τ x => VAR x] acts as identity on
    semantic environments.
*)
Lemma sem_subst_id {Γ : Env} (γ : sem_env Γ) :
    sem_subst (fun τ x => VAR x) γ = γ.
Proof.
  apply sem_env_ext. intros τ x.
  rewrite sem_subst_var. reflexivity.
Qed.


(* ================================================================== *)
(*   §7  Computation rules (β-rules)                                  *)
(* ================================================================== *)
(*
    These confirm that the denotation computes as expected on each
    constructor.  All follow by [reflexivity] except [sem_val_FIX_unfold],
    which uses [FIXP_is_fixedpoint] to unfold the recursive definition.

    These are the main interface used by [PCF_Soundness.v].
*)


(* -- Value computation rules ----------------------------------------- *)

Lemma sem_val_NLIT {Γ : Env} (n : nat) (γ : sem_env Γ) :
    sem_val (NLIT n) γ = n.
Proof. reflexivity. Qed.

Lemma sem_val_BLIT {Γ : Env} (b : bool) (γ : sem_env Γ) :
    sem_val (BLIT b) γ = b.
Proof. reflexivity. Qed.

Lemma sem_val_VAR {Γ : Env} {τ : Ty} (x : Var Γ τ) :
    sem_val (VAR x) = sem_var x.
Proof. reflexivity. Qed.

Lemma sem_val_PAIR {Γ : Env} {τ₁ τ₂ : Ty}
    (v₁ : Value Γ τ₁) (v₂ : Value Γ τ₂) (γ : sem_env Γ) :
    sem_val (PAIR v₁ v₂) γ = (sem_val v₁ γ, sem_val v₂ γ).
Proof. reflexivity. Qed.


(* -- Expressions ---------------------------------------------------- *)

Lemma sem_exp_VAL {Γ : Env} {τ : Ty} (v : Value Γ τ) :
    sem_exp (VAL v) = cont_comp (ret (D := sem_ty τ)) (sem_val v).
Proof. reflexivity. Qed.

Lemma sem_exp_LET {Γ : Env} {τ₁ τ₂ : Ty}
    (e₁ : Exp Γ τ₁) (e₂ : Exp (τ₁ :: Γ) τ₂) (γ : sem_env Γ) :
    sem_exp (LET e₁ e₂) γ =
      match sem_exp e₁ γ with
      | None => None
      | Some x => sem_exp e₂ (x, γ)
      end.
Proof. simpl. destruct (sem_exp e₁ γ); reflexivity. Qed.

Lemma sem_exp_APP {Γ : Env} {τ₁ τ₂ : Ty}
    (v₁ : Value Γ (τ₁ →ₜ τ₂)) (v₂ : Value Γ τ₁) (γ : sem_env Γ) :
    sem_exp (APP v₁ v₂) γ = sem_val v₁ γ (sem_val v₂ γ).
Proof. reflexivity. Qed.

Lemma sem_exp_FST {Γ : Env} {τ₁ τ₂ : Ty}
    (v : Value Γ (τ₁ ×ₜ τ₂)) (γ : sem_env Γ) :
    sem_exp (FST v) γ = Some (fst (sem_val v γ)).
Proof. reflexivity. Qed.

Lemma sem_exp_SND {Γ : Env} {τ₁ τ₂ : Ty}
    (v : Value Γ (τ₁ ×ₜ τ₂)) (γ : sem_env Γ) :
    sem_exp (SND v) γ = Some (snd (sem_val v γ)).
Proof. reflexivity. Qed.

Lemma sem_exp_OP {Γ : Env} (op : nat -> nat -> nat)
    (v₁ v₂ : Value Γ Nat) (γ : sem_env Γ) :
    sem_exp (OP op v₁ v₂) γ = Some (op (sem_val v₁ γ) (sem_val v₂ γ)).
Proof. reflexivity. Qed.

Lemma sem_exp_GT {Γ : Env} (v₁ v₂ : Value Γ Nat) (γ : sem_env Γ) :
    sem_exp (GT v₁ v₂) γ = Some (Nat.ltb (sem_val v₂ γ) (sem_val v₁ γ)).
Proof. reflexivity. Qed.

Lemma sem_exp_IFB {Γ : Env} {τ : Ty}
    (v : Value Γ Bool) (e₁ e₂ : Exp Γ τ) (γ : sem_env Γ) :
    sem_exp (IFB v e₁ e₂) γ =
      if sem_val v γ then sem_exp e₁ γ else sem_exp e₂ γ.
Proof. reflexivity. Qed.

(*  Split variants for when the branch is known. *)
Lemma sem_exp_IFB_true {Γ : Env} {τ : Ty}
    (v : Value Γ Bool) (e₁ e₂ : Exp Γ τ) (γ : sem_env Γ) :
    sem_val v γ = true ->
    sem_exp (IFB v e₁ e₂) γ = sem_exp e₁ γ.
Proof. intro H; rewrite sem_exp_IFB, H; reflexivity. Qed.

Lemma sem_exp_IFB_false {Γ : Env} {τ : Ty}
    (v : Value Γ Bool) (e₁ e₂ : Exp Γ τ) (γ : sem_env Γ) :
    sem_val v γ = false ->
    sem_exp (IFB v e₁ e₂) γ = sem_exp e₂ γ.
Proof. intro H; rewrite sem_exp_IFB, H; reflexivity. Qed.


(* -- FIX unfold ----------------------------------------------------- *)
(*
    The recursive case unfolds by [FIXP_is_fixedpoint]: the denotation of
    [FIX τ₁ τ₂ body] applied to [x] equals the body denotation at
    [(x, (sem_val (FIX ...) γ, γ))].
*)

Lemma sem_val_FIX_unfold {Γ : Env} {τ₁ τ₂ : Ty}
    (body : Exp (τ₁ :: (τ₁ →ₜ τ₂) :: Γ) τ₂)
    (γ : sem_env Γ) (x : sem_ty τ₁) :
    sem_val (FIX τ₁ τ₂ body) γ x =
      sem_exp body (x, (sem_val (FIX τ₁ τ₂ body) γ, γ)).
Proof.
  set (G := cont_flip (cont_curry (cont_flip (cont_curry (sem_exp body))))).
  set (F := G γ).
  (* Goal: FIXP F x = sem_exp body (x, (FIXP F, γ)).
     Key fact: F h x = sem_exp body (x, (h, γ)) by computation.
     So F (FIXP F) x = sem_exp body (x, (FIXP F, γ)) (reflexivity),
     and FIXP_is_fixedpoint F : F (FIXP F) = FIXP F transports this. *)
  exact (eq_ind (F (FIXP F))
    (fun g : sem_arrow_pointed τ₁ τ₂ => g x = sem_exp body (x, (FIXP F, γ)))
    eq_refl
    (FIXP F)
    (FIXP_is_fixedpoint F)).
Qed.


(* ================================================================== *)
(*   §8  Semantic renaming and weakening                              *)
(* ================================================================== *)
(*
    [sem_ren ρ] encodes a renaming [ρ : Ren Γ Γ'] as a semantic
    substitution.  From this we derive:

      [sem_ren_ext]:               renaming commutes with env extension
      [sem_val_ren / sem_exp_ren]: renaming commutes with sem_val/sem_exp
                                   (mutual induction)
      [sem_ren_wk]:                weakening drops the outermost component
      [sem_val_wk]:                corollary for value weakening
*)

Definition sem_ren {Γ Γ' : Env} (ρ : Ren Γ Γ')
    : cont_fun (sem_env Γ') (sem_env Γ) :=
  sem_subst (fun τ x => VAR (ρ τ x)).

Lemma sem_ren_var {Γ Γ' : Env} {τ : Ty}
    (ρ : Ren Γ Γ') (x : Var Γ τ) (γ' : sem_env Γ') :
    sem_var x (sem_ren ρ γ') = sem_var (ρ τ x) γ'.
Proof. unfold sem_ren. rewrite sem_subst_var. reflexivity. Qed.

Lemma sem_ren_ext {Γ Γ' : Env} {τ : Ty}
    (ρ : Ren Γ Γ') (x : sem_ty τ) (γ' : sem_env Γ') :
    sem_ren (ren_ext ρ) (x, γ') = (x, sem_ren ρ γ').
Proof.
  unfold sem_ren.
  change
    (((sem_val (VAR (ren_ext ρ _ ZVAR)) (x, γ'),
       sem_subst (fun τ0 y => VAR (ren_ext ρ τ0 (SVAR y))) (x, γ'))
      : sem_env (τ :: Γ)) =
     (x, sem_subst (fun τ0 y => VAR (ρ τ0 y)) γ')).
  apply injective_projections; cbn [fst snd].
  - reflexivity.
  - apply sem_env_ext. intros σ v.
    rewrite sem_subst_var.
    symmetry. rewrite sem_subst_var.
    reflexivity.
Qed.

Opaque sem_ren.

Lemma sem_val_ren : forall {Γ : Env} {τ : Ty} (v : Value Γ τ)
    {Γ' : Env} (ρ : Ren Γ Γ') (γ' : sem_env Γ'),
    sem_val (renVal ρ v) γ' = sem_val v (sem_ren ρ γ')
with sem_exp_ren : forall {Γ : Env} {τ : Ty} (e : Exp Γ τ)
    {Γ' : Env} (ρ : Ren Γ Γ') (γ' : sem_env Γ'),
    sem_exp (renExp ρ e) γ' = sem_exp e (sem_ren ρ γ').
Proof.
  { destruct v as [? n | ? b | ? ? x | ? τ₁ τ₂ body | ? ? ? v₁ v₂];
    intros Γ' ρ γ'.
    - reflexivity.
    - reflexivity.
    - symmetry. apply sem_ren_var.
    - (* FIX *)
      apply cont_fun_ext. intro arg.
      assert (H :
        cont_flip (cont_curry (cont_flip (cont_curry
            (sem_exp (renExp (ren_ext (ren_ext ρ)) body))))) γ'
        = cont_flip (cont_curry (cont_flip (cont_curry
            (sem_exp body)))) (sem_ren ρ γ')).
      { apply cont_fun_ext. intro h.
        apply cont_fun_ext. intro a.
        change (sem_exp (renExp (ren_ext (ren_ext ρ)) body) (a, (h, γ'))
              = sem_exp body (a, (h, sem_ren ρ γ'))).
        exact (eq_trans
          (sem_exp_ren _ _ body _ (ren_ext (ren_ext ρ)) (a, (h, γ')))
          (f_equal (fun γ => sem_exp body γ)
            (eq_trans
              (@sem_ren_ext _ _ τ₁ (ren_ext ρ) a (h, γ'))
              (f_equal (pair a) (sem_ren_ext ρ h γ'))))). }
      change (FIXP
        (cont_flip (cont_curry (cont_flip (cont_curry
            (sem_exp (renExp (ren_ext (ren_ext ρ)) body))))) γ') arg
        = FIXP
        (cont_flip (cont_curry (cont_flip (cont_curry
            (sem_exp body)))) (sem_ren ρ γ')) arg).
      rewrite H. reflexivity.
    - (* PAIR *)
      change ((sem_val (renVal ρ v₁) γ', sem_val (renVal ρ v₂) γ')
            = (sem_val v₁ (sem_ren ρ γ'), sem_val v₂ (sem_ren ρ γ'))).
      rewrite !sem_val_ren. reflexivity. }
  { destruct e as [? ? v | ? σ₁ σ₂ e₁ e₂ | ? σ₁ σ₂ v₁ v₂
                  | ? σ₁ σ₂ v | ? σ₁ σ₂ v
                  | ? op v₁ v₂ | ? v₁ v₂ | ? ? v e₁ e₂];
    intros Γ' ρ γ'.
    - change (Some (sem_val (renVal ρ v) γ')
            = Some (sem_val v (sem_ren ρ γ'))).
      rewrite sem_val_ren. reflexivity.
    - change (match sem_exp (renExp ρ e₁) γ' with
              | Some a => sem_exp (renExp (ren_ext ρ) e₂) (a, γ')
              | None => None end
            = match sem_exp e₁ (sem_ren ρ γ') with
              | Some a => sem_exp e₂ (a, sem_ren ρ γ')
              | None => None end).
      rewrite sem_exp_ren.
      destruct (sem_exp e₁ (sem_ren ρ γ')); [|reflexivity].
      rewrite sem_exp_ren, sem_ren_ext. reflexivity.
    - change (sem_val (renVal ρ v₁) γ' (sem_val (renVal ρ v₂) γ')
            = sem_val v₁ (sem_ren ρ γ') (sem_val v₂ (sem_ren ρ γ'))).
      rewrite !sem_val_ren. reflexivity.
    - change (Some (fst (sem_val (renVal ρ v) γ'))
            = Some (fst (sem_val v (sem_ren ρ γ')))).
      rewrite sem_val_ren. reflexivity.
    - change (Some (snd (sem_val (renVal ρ v) γ'))
            = Some (snd (sem_val v (sem_ren ρ γ')))).
      rewrite sem_val_ren. reflexivity.
    - change (Some (op (sem_val (renVal ρ v₁) γ') (sem_val (renVal ρ v₂) γ'))
            = Some (op (sem_val v₁ (sem_ren ρ γ'))
                       (sem_val v₂ (sem_ren ρ γ')))).
      rewrite !sem_val_ren. reflexivity.
    - change (Some (Nat.ltb (sem_val (renVal ρ v₂) γ')
                            (sem_val (renVal ρ v₁) γ'))
            = Some (Nat.ltb (sem_val v₂ (sem_ren ρ γ'))
                            (sem_val v₁ (sem_ren ρ γ')))).
      rewrite !sem_val_ren. reflexivity.
    - change ((if sem_val (renVal ρ v) γ'
               then sem_exp (renExp ρ e₁) γ'
               else sem_exp (renExp ρ e₂) γ')
            = (if sem_val v (sem_ren ρ γ')
               then sem_exp e₁ (sem_ren ρ γ')
               else sem_exp e₂ (sem_ren ρ γ'))).
      rewrite sem_val_ren, !sem_exp_ren. reflexivity. }
Qed.

Transparent sem_ren.

Lemma sem_ren_wk {Γ : Env} {τ : Ty} (x : sem_ty τ) (γ : sem_env Γ) :
    sem_ren (@ren_wk Γ τ) (x, γ) = γ.
Proof.
  apply sem_env_ext. intros σ v.
  rewrite sem_ren_var. reflexivity.
Qed.

Lemma sem_val_wk {Γ : Env} {τ σ : Ty}
    (v : Value Γ τ) (x : sem_ty σ) (γ : sem_env Γ) :
    sem_val (wkVal v) (x, γ) = sem_val v γ.
Proof.
  unfold wkVal. rewrite sem_val_ren, sem_ren_wk. reflexivity.
Qed.

(* ================================================================== *)
(*   §9  Substitution extension, substitution lemmas, and corollaries *)
(* ================================================================== *)

Lemma sem_subst_ext {Γ Γ' : Env} {τ : Ty}
    (σ : Subst Γ Γ') (x : sem_ty τ) (γ' : sem_env Γ') :
    sem_subst (subst_ext σ) (x, γ') = (x, sem_subst σ γ').
Proof.
  change
    (((sem_val (subst_ext σ _ ZVAR) (x, γ'),
       sem_subst (fun τ0 y => subst_ext σ τ0 (SVAR y)) (x, γ'))
      : sem_env (τ :: Γ)) =
     (x, sem_subst σ γ')).
  apply injective_projections; cbn [fst snd].
  - reflexivity.
  - apply sem_env_ext. intros ρ v.
    rewrite sem_subst_var.
    change (sem_val (wkVal (σ ρ v)) (x, γ') = sem_var v (sem_subst σ γ')).
    rewrite sem_val_wk.
    symmetry. rewrite sem_subst_var.
    reflexivity.
Qed.

(*
    The substitution lemmas are the semantic counterpart of [substVal] /
    [substExp] from [PCF_Syntax.v].  Used in [PCF_Soundness.v].

    Core invariant:
        sem_val (substVal σ v) γ' = sem_val v (sem_subst σ γ')
        sem_exp (substExp σ e) γ' = sem_exp e (sem_subst σ γ')

    The proof mirrors [sem_val_ren / sem_exp_ren], replacing renamings
    with substitutions throughout.  Each case uses [change] to expose
    the head normal form of [substVal σ _] / [substExp σ _], then
    rewrites with the IH.  The [VAR] case appeals to [sem_subst_var],
    and the [FIX] case uses [sem_subst_ext] twice.
*)

Lemma sem_val_subst : forall {Γ : Env} {τ : Ty} (v : Value Γ τ)
    {Γ' : Env} (σ : Subst Γ Γ') (γ' : sem_env Γ'),
    sem_val (substVal σ v) γ' = sem_val v (sem_subst σ γ')
with sem_exp_subst : forall {Γ : Env} {τ : Ty} (e : Exp Γ τ)
    {Γ' : Env} (σ : Subst Γ Γ') (γ' : sem_env Γ'),
    sem_exp (substExp σ e) γ' = sem_exp e (sem_subst σ γ').
Proof.
  { destruct v as [? n | ? b | ? ? x | ? τ₁ τ₂ body | ? ? ? v₁ v₂];
    intros Γ' σ γ'.
    - reflexivity.
    - reflexivity.
    - simpl. symmetry. apply sem_subst_var.
    - (* FIX *)
      apply cont_fun_ext. intro arg.
      assert (H :
        cont_flip (cont_curry (cont_flip (cont_curry
            (sem_exp (substExp (subst_ext (subst_ext σ)) body))))) γ'
        = cont_flip (cont_curry (cont_flip (cont_curry
            (sem_exp body)))) (sem_subst σ γ')).
      { apply cont_fun_ext. intro h.
        apply cont_fun_ext. intro a.
        change (sem_exp (substExp (subst_ext (subst_ext σ)) body) (a, (h, γ'))
              = sem_exp body (a, (h, sem_subst σ γ'))).
        exact (eq_trans
          (sem_exp_subst _ _ body _ (subst_ext (subst_ext σ)) (a, (h, γ')))
          (f_equal (fun γ => sem_exp body γ)
            (eq_trans
              (@sem_subst_ext _ _ τ₁ (subst_ext σ) a (h, γ'))
              (f_equal (pair a) (sem_subst_ext σ h γ'))))). }
      change (FIXP
        (cont_flip (cont_curry (cont_flip (cont_curry
            (sem_exp (substExp (subst_ext (subst_ext σ)) body))))) γ') arg
        = FIXP
        (cont_flip (cont_curry (cont_flip (cont_curry
            (sem_exp body)))) (sem_subst σ γ')) arg).
      rewrite H. reflexivity.
    - (* PAIR *)
      change ((sem_val (substVal σ v₁) γ', sem_val (substVal σ v₂) γ')
            = (sem_val v₁ (sem_subst σ γ'), sem_val v₂ (sem_subst σ γ'))).
      rewrite !sem_val_subst. reflexivity. }
  { destruct e as [? ? v | ? σ₁ σ₂ e₁ e₂ | ? σ₁ σ₂ v₁ v₂
                  | ? σ₁ σ₂ v | ? σ₁ σ₂ v
                  | ? op v₁ v₂ | ? v₁ v₂ | ? ? v e₁ e₂];
    intros Γ' σ γ'.
    - change (Some (sem_val (substVal σ v) γ')
            = Some (sem_val v (sem_subst σ γ'))).
      rewrite sem_val_subst. reflexivity.
    - change (match sem_exp (substExp σ e₁) γ' with
              | Some a => sem_exp (substExp (subst_ext σ) e₂) (a, γ')
              | None => None end
            = match sem_exp e₁ (sem_subst σ γ') with
              | Some a => sem_exp e₂ (a, sem_subst σ γ')
              | None => None end).
      rewrite sem_exp_subst.
      destruct (sem_exp e₁ (sem_subst σ γ')); [|reflexivity].
      rewrite sem_exp_subst, sem_subst_ext. reflexivity.
    - change (sem_val (substVal σ v₁) γ' (sem_val (substVal σ v₂) γ')
            = sem_val v₁ (sem_subst σ γ') (sem_val v₂ (sem_subst σ γ'))).
      rewrite !sem_val_subst. reflexivity.
    - change (Some (fst (sem_val (substVal σ v) γ'))
            = Some (fst (sem_val v (sem_subst σ γ')))).
      rewrite sem_val_subst. reflexivity.
    - change (Some (snd (sem_val (substVal σ v) γ'))
            = Some (snd (sem_val v (sem_subst σ γ')))).
      rewrite sem_val_subst. reflexivity.
    - change (Some (op (sem_val (substVal σ v₁) γ') (sem_val (substVal σ v₂) γ'))
            = Some (op (sem_val v₁ (sem_subst σ γ'))
                       (sem_val v₂ (sem_subst σ γ')))).
      rewrite !sem_val_subst. reflexivity.
    - change (Some (Nat.ltb (sem_val (substVal σ v₂) γ')
                            (sem_val (substVal σ v₁) γ'))
            = Some (Nat.ltb (sem_val v₂ (sem_subst σ γ'))
                            (sem_val v₁ (sem_subst σ γ')))).
      rewrite !sem_val_subst. reflexivity.
    - change ((if sem_val (substVal σ v) γ'
               then sem_exp (substExp σ e₁) γ'
               else sem_exp (substExp σ e₂) γ')
            = (if sem_val v (sem_subst σ γ')
               then sem_exp e₁ (sem_subst σ γ')
               else sem_exp e₂ (sem_subst σ γ'))).
      rewrite sem_val_subst, !sem_exp_subst. reflexivity. }
Qed.


(* -- Single and double substitution corollaries ---------------------- *)
(*
    Corollaries for the two operational substitutions from [PCF_Syntax.v].

    Both proofs use [transitivity] to introduce an explicit pair
    intermediate, then [change] to unfold [sem_subst] one step (via
    kernel conversion), and [injective_projections; cbn [fst snd]] to
    split the pair.  The head component closes by [reflexivity] (kernel
    conversion reduces e.g. [single_subst v _ ZVAR] to [v] because
    [var_case] computes by pure iota+beta).  The tail uses
    [sem_env_ext] + [sem_subst_var] + [reflexivity] pointwise.
*)

Lemma sem_subst_single {Γ : Env} {τ : Ty} (v : Value Γ τ) :
    sem_subst (single_subst v) =
      cont_pair (sem_val v) (cont_id (sem_env Γ)).
Proof.
  apply cont_fun_ext; intro γ.
  transitivity (sem_val v γ, γ : sem_env Γ).
  - change
      (sem_subst (single_subst v) γ = (sem_val v γ, γ))
    with
      ((sem_val (single_subst v _ ZVAR) γ,
        sem_subst (fun τ0 x => single_subst v τ0 (SVAR x)) γ) =
       (sem_val v γ, γ)).
    apply injective_projections; cbn [fst snd].
    + reflexivity.
    + apply sem_env_ext. intros ρ x.
      rewrite sem_subst_var. reflexivity.
  - reflexivity.
Qed.

Lemma sem_subst_double {Γ : Env} {τ₁ τ₂ : Ty}
    (varg : Value Γ τ₁) (vfun : Value Γ (τ₁ →ₜ τ₂)) :
    sem_subst (double_subst varg vfun) =
      cont_pair
        (sem_val varg)
        (cont_pair (sem_val vfun) (cont_id (sem_env Γ))).
Proof.
  apply cont_fun_ext; intro γ.
  transitivity (sem_val varg γ, (sem_val vfun γ, γ : sem_env Γ)).
  - change
      (sem_subst (double_subst varg vfun) γ =
       (sem_val varg γ, (sem_val vfun γ, γ)))
    with
      ((sem_val (double_subst varg vfun _ ZVAR) γ,
        sem_subst (fun τ0 x => double_subst varg vfun τ0 (SVAR x)) γ) =
       (sem_val varg γ, (sem_val vfun γ, γ))).
    apply injective_projections; cbn [fst snd].
    + reflexivity.
    + change
        (sem_subst (fun τ0 x => double_subst varg vfun τ0 (SVAR x)) γ =
         (sem_val vfun γ, γ))
      with
        ((sem_val (double_subst varg vfun _ (SVAR ZVAR)) γ,
          sem_subst (fun τ0 x => double_subst varg vfun τ0 (SVAR (SVAR x))) γ) =
         (sem_val vfun γ, γ)).
      apply injective_projections; cbn [fst snd].
      * reflexivity.
      * apply sem_env_ext. intros ρ x.
        rewrite sem_subst_var. reflexivity.
  - reflexivity.
Qed.