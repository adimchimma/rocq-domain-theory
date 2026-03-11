(*  PCF_Adequacy

    Phase 1: Computational adequacy for typed call-by-value PCF (PCFv).

    This is [src/lang/PCF_Adequacy.v].

    Imports:
      [src/lang/PCF_Syntax.v]        — Ty, Env, Value, Exp, CValue, CExp,
                                        Var, FIX, PAIR, NLIT, BLIT, VAR,
                                        singleSubstExp, doubleSubstExp,
                                        substVal, substExp, Subst,
                                        subst_ext, single_subst, double_subst
      [src/lang/PCF_Operational.v]   — Eval (e ⇓ v), Converges (e ⇓),
                                        e_Val, e_Let, e_App, e_Fst, e_Snd,
                                        e_Op, e_Gt, e_IfTrue, e_IfFalse,
                                        eval_converges, val_converges
      [src/lang/PCF_Denotational.v]  — sem_ty, sem_env, sem_val, sem_exp,
                                        sem_cval, sem_cexp, sem_var,
                                        sem_val_FIX_unfold,
                                        sem_subst_single, sem_subst_double,
                                        sem_val_subst, sem_exp_subst,
                                        sem_val_NLIT, sem_val_BLIT,
                                        sem_val_PAIR, sem_exp_LET,
                                        sem_exp_APP, sem_exp_IFB,
                                        sem_env_ext, sem_subst_id,
                                        sem_subst_ext, sem_subst_var
      [src/lang/PCF_Soundness.v]     — soundness
      [src/structures/CPO.v]         — CPO.type, PointedCPO.type
      [src/structures/Morphisms.v]   — cont_fun
      [src/theory/Lift.v]            — lift_le, lift_le_some_iff,
                                        lift_none_le, lift_some_not_le_none,
                                        lift_sup_none, lift_sup_some_eq,
                                        chain_some_stable,
                                        extract_some, some_of_extract,
                                        D_chain, kleisli
      [src/theory/FixedPoints.v]     — fixp, fixp_ind, iter,
                                        kleene_chain, iter_le_fixp
      [src/theory/FunctionSpaces.v]  — FIXP, FIXP_is_fixedpoint,
                                        fun_bottom, fun_bottom_least,
                                        cont_curry, cont_eval
      [src/theory/CPOTheory.v]       — admissible, admissible_forall,
                                        admissible_true, admissible_preimage,
                                        admissible_and
      [src/instances/Discrete.v]     — nat and bool discrete CPO instances
      [src/instances/Function.v]     — cont_ap, cont_flip

    Summary
    =======
    We prove computational adequacy — the converse of soundness:

        Theorem adequacy :
          forall τ (e : CExp τ),
            sem_exp e tt <> None  ->  e ⇓.

    Combined with [soundness] from [PCF_Soundness.v], this gives the
    full operational/denotational correspondence:

        e ⇓  <->  sem_exp e tt <> None

    Proof strategy: logical relation
    =================================
    Following Benton–Kennedy–Varming §3.2.

    We define a type-indexed logical relation:

        rel_val τ : sem_ty τ → CValue τ → Prop
        rel_exp τ : option (sem_ty τ) → CExp τ → Prop

    where [rel_exp] is the "lift" of [rel_val]:
        rel_exp τ None     e  :=  True
        rel_exp τ (Some d) e  :=  ∃ v, e ⇓ v  ∧  rel_val τ d v

    The base cases:
        rel_val Nat  n  v   :=  v = NLIT n
        rel_val Bool b  v   :=  v = BLIT b

    The arrow case:
        rel_val (τ₁ →ₜ τ₂) f v  :=
          ∃ body, v = FIX τ₁ τ₂ body  ∧
          ∀ d₁ v₁, rel_val τ₁ d₁ v₁ →
            rel_exp τ₂ (f d₁) (doubleSubstExp v₁ v body)

    The product case:
        rel_val (τ₁ ×ₜ τ₂) (d₁, d₂) v  :=
          ∃ v₁ v₂, v = PAIR v₁ v₂  ∧  rel_val τ₁ d₁ v₁  ∧  rel_val τ₂ d₂ v₂

    The fundamental lemma (proved by mutual induction on syntax) shows
    that every well-typed term, instantiated by a related environment,
    lies in the logical relation.  For closed terms this immediately
    gives adequacy.

    The hard case is [FIX]: the denotation is a Kleene fixed point, and
    we apply Scott's fixed-point induction principle [fixp_ind] with
    the predicate:

      P(h) := ∀ d₁ v₁, rel_val τ₁ d₁ v₁ →
                rel_exp τ₂ (h d₁) (doubleSubstExp v₁ v_fix body')

    where admissibility follows from [admissible_preimage] composed
    with [rel_exp_admissible].

    Contents:
    - §1  The logical relation
    - §2  Admissibility of [rel_exp]
    - §3  The fundamental lemma (mutual induction on syntax)
    - §4  Adequacy theorem
    - §5  Full correspondence

    Phase coverage:
      Phase 1 — all sections.

    References:
      Benton, Kennedy, Varming — "Some Domain Theory and Denotational
        Semantics in Coq", §3.2, Theorems [Soundness] and [Adequacy].
*)

From Stdlib Require Import List PeanoNat Bool Program.Equality Classical.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import
  Lift CPOTheory FixedPoints FunctionSpaces.
From DomainTheory.Instances Require Import Discrete Function.
From DomainTheory.Lang Require Import
  PCF_Syntax
  PCF_Operational
  PCF_Denotational
  PCF_Soundness.

Import ListNotations.
Local Open Scope type_scope.


(* ================================================================== *)
(*   §1  The logical relation                                          *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(*   §1a  Value and expression relations, defined by mutual recursion  *)
(*        on types                                                     *)
(* ------------------------------------------------------------------ *)
(*
    [rel_val τ d v] relates a denotation [d : sem_ty τ] to a closed
    syntactic value [v : CValue τ].

    [rel_exp τ o e] is the "lift" of [rel_val] to the option type:
    it relates [o : option (sem_ty τ)] to a closed expression [e : CExp τ].

    Both are defined by structural recursion on [τ].

    Arrow case: a function denotation [f] is related to [v] iff
      [v = FIX τ₁ τ₂ body] for some body, and for all related inputs
      [(d₁, v₁)], the application denotation is related to the
      syntactic application — i.e. to [doubleSubstExp v₁ v body]
      which is what [e_App] evaluates [APP v v₁] to.

    Product case: [(d₁, d₂)] is related to [v] iff [v = PAIR v₁ v₂]
      with each component related.
*)

Fixpoint rel_val (τ : Ty) : sem_ty τ -> CValue τ -> Prop :=
  match τ return sem_ty τ -> CValue τ -> Prop with

  | Nat =>
      fun d v => v = NLIT d

  | Bool =>
      fun b v => v = BLIT b

  | Arrow τ₁ τ₂ =>
      fun f v =>
        exists body : Exp [τ₁ ; τ₁ →ₜ τ₂] τ₂,
          v = FIX τ₁ τ₂ body /\
          forall (d₁ : sem_ty τ₁) (v₁ : CValue τ₁),
            rel_val τ₁ d₁ v₁ ->
            match (f d₁) with
            | None   => True
            | Some d => exists w : CValue τ₂,
                          doubleSubstExp v₁ v body ⇓ w /\ rel_val τ₂ d w
            end

  | Prod τ₁ τ₂ =>
      fun '(d₁, d₂) v =>
        exists (v₁ : CValue τ₁) (v₂ : CValue τ₂),
          v = PAIR v₁ v₂ /\
          rel_val τ₁ d₁ v₁ /\
          rel_val τ₂ d₂ v₂

  end.

Definition rel_exp (τ : Ty) (o : option (sem_ty τ)) (e : CExp τ) : Prop :=
  match o with
  | None   => True
  | Some d => exists v : CValue τ, e ⇓ v /\ rel_val τ d v
  end.


(* ------------------------------------------------------------------ *)
(*   §1b  Computed equations for [rel_exp]                             *)
(* ------------------------------------------------------------------ *)

Lemma rel_exp_none {τ : Ty} (e : CExp τ) :
    rel_exp τ None e.
Proof.
  exact I.
Qed.

Lemma rel_exp_some_iff {τ : Ty} (d : sem_ty τ) (e : CExp τ) :
    rel_exp τ (Some d) e <->
    exists v : CValue τ, e ⇓ v /\ rel_val τ d v.
Proof.
  reflexivity.
Qed.

(*  Convergence witnesses from rel_exp. *)
Lemma rel_exp_some_converges {τ : Ty} (d : sem_ty τ) (e : CExp τ) :
    rel_exp τ (Some d) e -> e ⇓.
Proof.
  rewrite rel_exp_some_iff.
  intros [v [Hv _]]. exact (eval_converges e v Hv).
Qed.

(*  Constructor for rel_exp from evaluation + rel_val. *)
Lemma rel_exp_intro {τ : Ty} (d : sem_ty τ) (e : CExp τ) (v : CValue τ) :
    e ⇓ v -> rel_val τ d v -> rel_exp τ (Some d) e.
Proof.
  intros Hev Hrel.
  rewrite rel_exp_some_iff. exists v. exact (conj Hev Hrel).
Qed.


(* ================================================================== *)
(*   §2  Admissibility of [rel_exp]                                   *)
(* ================================================================== *)
(*
    We need [fun o => rel_exp τ o e] to be admissible as a predicate on
    [option (sem_ty τ)] — this is required for the [fixp_ind] step in
    the FIX case of the fundamental lemma.

    The argument:
    - If the chain [c] in [option (sem_ty τ)] is always [None], then
      [⊔ c = None] (by [lift_sup_none]) and [rel_exp τ None e = True].
    - If [c] eventually reaches [Some] at index N, then [⊔ c = Some ...]
      (by [lift_sup_some_eq]).  From [Hchain N] we extract a value
      witness [v] with [e ⇓ v].  We need to show the convergence witness
      works at the sup too — this is the hard part.

    For our logical relation, the convergence witness [v] does not depend
    on the chain position: once [e ⇓ v] at index N, the same [v] works
    everywhere (by [eval_deterministic]).  The rel_val condition at the
    sup follows from [rel_val_admissible], which shows that
    [fun d => rel_val τ d v] is an admissible predicate on [sem_ty τ].
*)

(*  Admissibility of [rel_val] in its denotational argument.

    Proof: by induction on τ.
    - Nat/Bool: the chain is constant (discrete CPO) so the sup
      equals [c.[0]].
    - Prod: componentwise, using IH for each component.
    - Arrow: for a chain [f_n] with [∀ n, rel_val _ f_n v]:
        The body is the same for all n (since v is fixed).
        For any related [(d₁, v₁)]:
          [(⊔ f_n) d₁ = ⊔ (f_n d₁)] (pointwise sup in the lift CPO)
        If all [f_n d₁] are None, then the sup is None and we're done.
        Otherwise, some [f_N d₁ = Some e_N], giving a witness [w] with
          [body ⇓ w] and [rel_val τ₂ e_N w].
        For later indices, [f_{N+k} d₁ = Some e_{N+k}] with
          [rel_val τ₂ e_{N+k} w] (same [w] by determinism).
        Then [⊔ (f_n d₁) = Some (⊔ D_chain ...)] and by IH
          ([rel_val_admissible] at τ₂) we get the result.           *)
Lemma rel_val_admissible :
    forall (τ : Ty) (v : CValue τ),
      admissible (fun d => rel_val τ d v).
Proof.
  induction τ as [| | τ₁ IHτ₁ τ₂ IHτ₂ | τ₁ IHτ₁ τ₂ IHτ₂];
    intros v c Hchain.
  - (* Nat: discrete, chain is constant *)
    simpl in *. rewrite nat_sup_eq. exact (Hchain 0).
  - (* Bool: discrete, chain is constant *)
    simpl in *. rewrite bool_sup_eq. exact (Hchain 0).
  - (* Arrow τ₁ τ₂ *)
    pose proof (Hchain 0) as Hchain0_raw.
    simpl rel_val in Hchain0_raw.
    destruct Hchain0_raw as [body [Hv Hrel0]].
    simpl rel_val.
    exists body. split; [exact Hv|].
    intros d₁ v₁ Hd₁.
    set (oc := pointwise_chain c d₁).
    assert (Hsup_rel : match ⊔ oc with
                       | Some d => exists w, doubleSubstExp v₁ v body ⇓ w /\ rel_val τ₂ d w
                       | None => True
                       end).
    { destruct (classic (exists N, oc.[N] <> None)) as [[N HN] | Hnone].
      + pose proof (Hchain N) as HchainN_raw.
        simpl rel_val in HchainN_raw.
        destruct HchainN_raw as [body' [HvN HrelN]].
        rewrite Hv in HvN.
        assert (body' = body).
        { injection HvN as Hinj.
          apply Eqdep.EqdepTheory.inj_pair2 in Hinj.
          apply Eqdep.EqdepTheory.inj_pair2 in Hinj.
          apply Eqdep.EqdepTheory.inj_pair2 in Hinj.
          exact (eq_sym Hinj). }
        subst body'.
        specialize (HrelN d₁ v₁ Hd₁).
        change (match oc.[N] with
                | Some d => exists w, doubleSubstExp v₁ v body ⇓ w /\ rel_val τ₂ d w
                | None => True
                end) in HrelN.
        pose proof (some_of_extract oc.[N] HN) as HocN.
        set (dN := extract_some oc.[N] HN).
        rewrite HocN in HrelN.
        destruct HrelN as [w [Hew Hrw]].
        (* For all k, oc.[N+k] gives rel_val τ₂ dNk w *)
        assert (Hchain_vals : forall k,
                  exists dNk, oc.[Nat.add N k] = Some dNk /\ rel_val τ₂ dNk w).
        { intros k.
          assert (Hstab : oc.[Nat.add N k] <> None)
            by (apply chain_some_stable; exact HN).
          pose proof (some_of_extract oc.[Nat.add N k] Hstab) as HocNk.
          pose proof (Hchain (Nat.add N k)) as HchainNk_raw.
          simpl rel_val in HchainNk_raw.
          destruct HchainNk_raw as [body'' [HvNk HrelNk]].
          rewrite Hv in HvNk.
          assert (body'' = body).
          { injection HvNk as Hinj.
            apply Eqdep.EqdepTheory.inj_pair2 in Hinj.
            apply Eqdep.EqdepTheory.inj_pair2 in Hinj.
            apply Eqdep.EqdepTheory.inj_pair2 in Hinj.
            exact (eq_sym Hinj). }
          subst body''.
          specialize (HrelNk d₁ v₁ Hd₁).
          change (match oc.[Nat.add N k] with
                  | Some d => exists w0, doubleSubstExp v₁ v body ⇓ w0 /\ rel_val τ₂ d w0
                  | None => True
                  end) in HrelNk.
          rewrite HocNk in HrelNk.
          destruct HrelNk as [w' [Hew' Hrw']].
          assert (w' = w) by (eapply eval_deterministic; eauto). subst w'.
          exists (extract_some oc.[Nat.add N k] Hstab).
          split; [exact HocNk|exact Hrw']. }
        (* Use lift_sup_some_eq to decompose ⊔ oc *)
        assert (Hlift : ⊔ oc = Some (⊔ (D_chain N dN oc HN)))
          by (apply lift_sup_some_eq).
        rewrite Hlift. simpl.
        exists w. split; [exact Hew|].
        (* Apply IHτ₂: need rel_val τ₂ (D_chain ...).[k] w for all k
           Key: (D_chain N dN oc HN).[k] = D_chain_fn N dN oc k
                = match oc.[N+k] with Some d => d | None => dN end
                = dNk (since oc.[N+k] = Some dNk) *)
        apply (IHτ₂ w).
        intros k.
        destruct (Hchain_vals k) as [dNk [HocNk Hrk]].
        (* Goal: rel_val τ₂ (D_chain N dN oc HN).[k] w
           We know D_chain_fn N dN oc k = dNk and (D_chain ...).[k] = D_chain_fn ... k *)
        assert (Helem : D_chain_fn N dN oc k = dNk).
        { (* D_chain_fn_eq gives us oc.[N+k] = Some (D_chain_fn N dN oc k)
             Combined with HocNk: oc.[Nat.add N k] = Some dNk, gives D_chain_fn ... = dNk *)
          pose proof (D_chain_fn_eq N dN oc k HN) as Hfn.
          (* Hfn : oc.[N+k] = Some (D_chain_fn N dN oc k) — same form as oc.[...] in HocNk *)
          assert (Some (D_chain_fn N dN oc k) = Some dNk) as Hinj.
          { transitivity (oc.[Nat.add N k]); [symmetry; exact Hfn | exact HocNk]. }
          injection Hinj. auto. }
        (* Transport via the definitional equality *)
        change ((D_chain N dN oc HN).[k]) with (D_chain_fn N dN oc k) in *.
        rewrite Helem. exact Hrk.
      + (* All None case *)
        assert (Hall : forall n, oc.[n] = None).
        { intros n. destruct (oc.[n]) eqn:E; [|reflexivity].
          exfalso. apply Hnone. exists n. rewrite E. discriminate. }
        assert (Hnone_sup : ⊔ oc = None) by (apply lift_sup_none; exact Hall).
        rewrite Hnone_sup. exact I. }
    (* Transfer: goal has expanded form of (⊔ c) d₁, which computes to ⊔ oc *)
    change (match ⊔ oc with
            | Some d => exists w, doubleSubstExp v₁ v body ⇓ w /\ rel_val τ₂ d w
            | None => True
            end).
    exact Hsup_rel.
  - (* Prod τ₁ τ₂ *)
    (* Goal: rel_val (τ₁ ×ₜ τ₂) (⊔ c) v. ⊔ c = (⊔ fst∘c, ⊔ snd∘c) is a pair. *)
    simpl rel_val.
    (* Goal is now: exists v₁ v₂, v = PAIR v₁ v₂ /\ rel_val τ₁ (fst (⊔ c)) v₁ /\ ... *)
    (* Extract v₁, v₂ from c.[0] *)
    pose proof (Hchain 0) as H0.
    destruct (c.[0]) as [d₁0 d₂0] eqn:Ec0.
    simpl rel_val in H0.
    destruct H0 as [v₁ [v₂ [Hv [Hr1_0 Hr2_0]]]].
    exists v₁, v₂. split; [exact Hv|].
    split.
    + (* rel_val τ₁ (fst (⊔ c)) v₁ = rel_val τ₁ (⊔ (map_chain fst_mono c)) v₁ *)
      apply (IHτ₁ v₁). intros n.
      pose proof (Hchain n) as Hn.
      destruct (c.[n]) as [d₁n d₂n] eqn:Ecn.
      simpl rel_val in Hn.
      destruct Hn as [v₁' [v₂' [Hv' [Hr1 Hr2]]]].
      rewrite Hv in Hv'. 
      dependent destruction Hv'.
      change ((map_chain Products.fst_mono c).[n]) with (fst (c.[n])).
      rewrite Ecn. simpl. exact Hr1.
    + apply (IHτ₂ v₂). intros n.
      pose proof (Hchain n) as Hn.
      destruct (c.[n]) as [d₁n d₂n] eqn:Ecn.
      simpl rel_val in Hn.
      destruct Hn as [v₁' [v₂' [Hv' [Hr1 Hr2]]]].
      rewrite Hv in Hv'.
      dependent destruction Hv'.
      change ((map_chain Products.snd_mono c).[n]) with (snd (c.[n])).
      rewrite Ecn. simpl. exact Hr2.
Qed.

(*  Admissibility of [rel_exp] in its denotational argument.          *)
Lemma rel_exp_admissible (τ : Ty) (e : CExp τ) :
    admissible (fun o => rel_exp τ o e).
Proof.
  intros c Hchain.
  unfold rel_exp.
  destruct (classic (exists N, c.[N] <> None)) as [[N HN] | Hnone].
  - (* Some case: c.[N] <> None, so ⊔ c = Some (⊔ D_chain ...) *)
    pose proof (some_of_extract c.[N] HN) as HcN.
    set (dN := extract_some c.[N] HN).
    pose proof (Hchain N) as HrelN. unfold rel_exp in HrelN.
    rewrite HcN in HrelN.
    destruct HrelN as [v [Hev Hrv]].
    (* All chain elements from N onward give the same v *)
    assert (Hchain_vals : forall k,
              exists dk, c.[Nat.add N k] = Some dk /\ rel_val τ dk v).
    { intros k.
      assert (Hstab : c.[Nat.add N k] <> None)
        by (apply chain_some_stable; exact HN).
      pose proof (some_of_extract c.[Nat.add N k] Hstab) as HcNk.
      pose proof (Hchain (Nat.add N k)) as HrelNk. unfold rel_exp in HrelNk.
      rewrite HcNk in HrelNk.
      destruct HrelNk as [v' [Hev' Hrv']].
      assert (v' = v) by (eapply eval_deterministic; eauto). subst v'.
      exists (extract_some c.[Nat.add N k] Hstab).
      split; [exact HcNk | exact Hrv']. }
    assert (Hlift : ⊔ c = Some (⊔ (D_chain N dN c HN)))
      by (apply lift_sup_some_eq).
    rewrite Hlift.
    exists v. split; [exact Hev|].
    apply (rel_val_admissible τ v).
    intros k.
    destruct (Hchain_vals k) as [dk [Hck Hrk]].
    assert (Helem : D_chain_fn N dN c k = dk).
    { pose proof (D_chain_fn_eq N dN c k HN) as Hfn.
      assert (Some (D_chain_fn N dN c k) = Some dk) as Hinj.
      { transitivity (c.[Nat.add N k]); [symmetry; exact Hfn | exact Hck]. }
      injection Hinj. auto. }
    change ((D_chain N dN c HN).[k]) with (D_chain_fn N dN c k).
    rewrite Helem. exact Hrk.
  - (* All None case *)
    assert (Hall : forall n, c.[n] = None).
    { intros n. destruct (c.[n]) eqn:E; [|reflexivity].
      exfalso. apply Hnone. exists n. rewrite E. discriminate. }
    assert (Hnone_sup : ⊔ c = None) by (apply lift_sup_none; exact Hall).
    rewrite Hnone_sup. exact I.
Qed.

(*  Pointwise admissibility for the FIX case.                          *)
Lemma rel_exp_admissible_pointwise (τ₁ τ₂ : Ty)
    (body  : Exp [τ₁ ; τ₁ →ₜ τ₂] τ₂)
    (v_fix : CValue (τ₁ →ₜ τ₂)) :
    admissible
      (fun (h : sem_ty (τ₁ →ₜ τ₂)) =>
         forall (d₁ : sem_ty τ₁) (v₁ : CValue τ₁),
           rel_val τ₁ d₁ v₁ ->
           rel_exp τ₂ (h d₁) (doubleSubstExp v₁ v_fix body)).
Proof.
  intros c Hchain d₁ v₁ Hd₁.
  (* Need: rel_exp τ₂ ((⊔ c) d₁) (doubleSubstExp v₁ v_fix body) *)
  (* (⊔ c) d₁ = ⊔ (pointwise_chain c d₁) *)
  set (oc := pointwise_chain c d₁).
  assert (Heq : (⊔ c) d₁ = ⊔ oc) by reflexivity.
  (* Each c.[n] d₁ = oc.[n], and Hchain n says rel_exp τ₂ (c.[n] d₁) ... *)
  apply (rel_exp_admissible τ₂ (doubleSubstExp v₁ v_fix body) oc).
  intros n.
  exact (Hchain n d₁ v₁ Hd₁).
Qed.


(* ================================================================== *)
(*   §3  The fundamental lemma                                        *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(*   §3a  Environment relation                                         *)
(* ------------------------------------------------------------------ *)
(*
    [rel_env Γ γ σ] — a semantic environment [γ : sem_env Γ] and a
    closed substitution [σ : Subst Γ []] are _related_ when, for every
    well-typed variable [x : Var Γ τ], the denotation [sem_var x γ] is
    related by [rel_val τ] to the syntactic value [σ _ x].
*)

Definition rel_env (Γ : Env) (γ : sem_env Γ) (σ : Subst Γ []) : Prop :=
  forall τ (x : Var Γ τ), rel_val τ (sem_var x γ) (σ _ x).

Lemma rel_env_nil : rel_env [] tt (fun _ x => match x with end).
Proof.
  intros τ x. dependent destruction x.
Qed.

(*  Extending a related environment at the head.                       *)
Lemma rel_env_cons {Γ : Env} {τ : Ty}
    (γ : sem_env Γ) (σ : Subst Γ [])
    (d : sem_ty τ) (v : CValue τ)
    (Henv : rel_env Γ γ σ)
    (Hd   : rel_val τ d v) :
    rel_env (τ :: Γ) (d, γ) (var_case v (fun ρ y => σ ρ y)).
Proof.
  intros τ' x. dependent destruction x.
  - simpl. exact Hd.
  - simpl. exact (Henv _ x).
Qed.

(*  Destruct a product relation into [fst]/[snd] components. *)
Lemma rel_val_prod_inv {τ₁ τ₂ : Ty}
    (p : sem_ty (Prod τ₁ τ₂)) (v : CValue (Prod τ₁ τ₂)) :
    rel_val (Prod τ₁ τ₂) p v ->
    exists (w₁ : CValue τ₁) (w₂ : CValue τ₂),
      v = PAIR w₁ w₂ /\ rel_val τ₁ (fst p) w₁ /\ rel_val τ₂ (snd p) w₂.
Proof.
  simpl. destruct p. auto.
Qed.


(* ------------------------------------------------------------------ *)
(*   §3b  Substitution-composition lemma for the FIX case             *)
(* ------------------------------------------------------------------ *)
(*
    In the FIX case of the fundamental lemma, we need to relate
    [substExp σ_ext body] to [doubleSubstExp v₁ v_fix body'] where
    [body' = substExp (subst_ext (subst_ext σ)) body].

    This is captured by:
      substExp σ_ext body = doubleSubstExp v₁ v_fix body'
    where σ_ext maps ZVAR ↦ v₁, SVAR ZVAR ↦ v_fix, SVAR (SVAR y) ↦ σ _ y.

    The proof proceeds by showing that [σ_ext] and
    [double_subst v₁ v_fix ∘ subst_ext (subst_ext σ)] agree on all
    variables, then using a substitution-extensionality lemma.
*)

Lemma subst_double_ext {Γ : Env} {τ₁ τ₂ : Ty}
    (σ : Subst Γ [])
    (v₁ : CValue τ₁)
    (v_fix : CValue (τ₁ →ₜ τ₂))
    (body : Exp (τ₁ :: (τ₁ →ₜ τ₂) :: Γ) τ₂) :
    let body' := substExp (subst_ext (subst_ext σ)) body in
    let σ_ext := var_case v₁ (var_case v_fix (fun ρ y => σ ρ y)) in
    substExp σ_ext body = doubleSubstExp v₁ v_fix body'.
Proof.
  simpl. unfold doubleSubstExp.
  rewrite substExp_comp.
  apply substExp_ext.
  intros τ x. dependent destruction x.
  - (* ZVAR *) reflexivity.
  - dependent destruction x.
    + (* SVAR ZVAR *) reflexivity.
    + (* SVAR (SVAR y) *)
      simpl. unfold wkVal.
      rewrite !substVal_renVal.
      simpl. symmetry. apply substVal_id.
Qed.

(*  Single-substitution variant for the LET case.                      *)
Lemma subst_single_ext {Γ : Env} {τ₁ τ₂ : Ty}
    (σ : Subst Γ [])
    (v₁ : CValue τ₁)
    (e₂ : Exp (τ₁ :: Γ) τ₂) :
    let e₂' := substExp (subst_ext σ) e₂ in
    substExp (var_case v₁ (fun ρ y => σ ρ y)) e₂ = singleSubstExp v₁ e₂'.
Proof.
  simpl. unfold singleSubstExp.
  rewrite substExp_comp.
  apply substExp_ext.
  intros τ x. dependent destruction x.
  - reflexivity.
  - simpl. unfold wkVal.
    rewrite substVal_renVal.
    simpl. symmetry. apply substVal_id.
Qed.


(* ------------------------------------------------------------------ *)
(*   §3c  Fundamental lemma statement and proof                       *)
(* ------------------------------------------------------------------ *)
(*
    Mutual induction on [Value Γ τ] and [Exp Γ τ].

    Because [Value] and [Exp] are mutually defined, we use the combined
    induction scheme generated by [Scheme .. Combined Scheme ..].

    For the FIX case we apply [fixp_ind] (Scott's induction principle)
    to the Kleene iterate chain of the semantic fixpoint functional.
*)

Scheme value_ind2 := Induction for Value Sort Prop
  with exp_ind2   := Induction for Exp   Sort Prop.
Combined Scheme val_exp_ind from value_ind2, exp_ind2.

Theorem fundamental_lemma :
    (forall {Γ : Env} {τ : Ty} (v : Value Γ τ)
         (σ : Subst Γ []) (γ : sem_env Γ),
         rel_env Γ γ σ ->
         rel_val τ (sem_val v γ) (substVal σ v))
  /\
    (forall {Γ : Env} {τ : Ty} (e : Exp Γ τ)
         (σ : Subst Γ []) (γ : sem_env Γ),
         rel_env Γ γ σ ->
         rel_exp τ (sem_exp e γ) (substExp σ e)).
Proof.
  apply val_exp_ind; intros.

  (* ---- Value cases ---- *)

  - (* NLIT *)
    simpl. reflexivity.

  - (* BLIT *)
    simpl. reflexivity.

  - (* VAR *)
    simpl. apply H.

  - (* FIX τ₁ τ₂ body *)
    simpl rel_val.
    set (body' := substExp (subst_ext (subst_ext σ)) e).
    exists body'.
    split; [reflexivity|].
    intros d₁ v₁ Hd₁.
    (*
       Goal: rel_exp τ₂ (sem_val (FIX τ₁ τ₂ e) γ d₁) (doubleSubstExp v₁ (FIX _ _ body') body').

       sem_val (FIX τ₁ τ₂ e) γ  =  fixp F₋  where F₋ operates on the 
       PointedCPO sem_arrow_pointed τ₁ τ₂.

       To avoid HB PointedCPO/CPO mismatch we reason via iterates directly.
       For each n, iter F₋ n is a cont_fun; we prove the property
       by nat induction and close with admissibility.
    *)
    (* Strengthen the goal: prove the property for ALL d and v *)
    enough (Hiter : forall (n : nat) (d : sem_ty τ₁) (w : CValue τ₁),
        rel_val τ₁ d w ->
        rel_exp τ₂ (iter (cont_flip (cont_curry (cont_flip (cont_curry (sem_exp e)))) γ) n d)
                (doubleSubstExp w (FIX _ _ body') body')).
    {
      (* Close from iterates to fixp via admissibility *)
      set (F := cont_flip (cont_curry (cont_flip (cont_curry (sem_exp e)))) γ).
      set (kc := kleene_chain F).
      set (pc := pointwise_chain kc d₁).
      apply (rel_exp_admissible τ₂ (doubleSubstExp v₁ (FIX _ _ body') body') pc).
      intros n. exact (Hiter n d₁ v₁ Hd₁).
    }
    (* Prove by nat induction *)
    induction n as [| n IHn].
    + (* Base: iter F 0 = ⊥ *)
      intros d w Hw. simpl. exact I.
    + (* Step: iter F (S n) = F (iter F n) *)
      intros d w Hw.
      simpl iter.
      set (v_fix := FIX _ _ body' : CValue (τ₁ →ₜ τ₂)).
      assert (Heq : substExp (var_case w (var_case v_fix (fun ρ y => σ ρ y))) e
                   = doubleSubstExp w v_fix body').
      { unfold body'. exact (subst_double_ext σ w v_fix e). }
      rewrite <- Heq.
      (* The iter term has PointedCPO.sort type; cast to sem_ty *)
      pose (h_n := (iter (cont_flip (cont_curry (cont_flip (cont_curry (sem_exp e)))) γ) n : sem_ty (Arrow τ₁ τ₂))).
      change (iter (cont_flip (cont_curry (cont_flip (cont_curry (sem_exp e)))) γ) n) with h_n.
      (* Debug: check if rel_env_cons works *)
      assert (Henv : rel_env (τ₁ :: Arrow τ₁ τ₂ :: Γ) (d, (h_n, γ))
                       (var_case w (var_case v_fix (fun ρ y => σ ρ y)))).
      { intros τ' x. dependent destruction x.
        - simpl. exact Hw.
        - dependent destruction x.
          + simpl. simpl rel_val. exists body'.
            split; [reflexivity|].
            exact IHn.
          + simpl. exact (H0 _ x). }
      exact (H _ _ Henv).

  - (* PAIR v v0 *)
    simpl. exists (substVal σ v), (substVal σ v0).
    split; [reflexivity|]. split; [exact (H _ _ H1) | exact (H0 _ _ H1)].

  (* ---- Expression cases ---- *)

  - (* VAL v *)
    simpl. exists (substVal σ v). split.
    + exact (e_Val _).
    + exact (H _ _ H0).

  - (* LET e e0 *)
    simpl substExp. rewrite sem_exp_LET.
    specialize (H σ γ H1) as He₁.
    destruct (sem_exp e γ) as [d₁|]; [|exact I].
    simpl in He₁. destruct He₁ as [w₁ [Heval₁ Hrel₁]].
    specialize (H0 _ _ (rel_env_cons γ σ d₁ w₁ H1 Hrel₁)) as He₂.
    rewrite (subst_single_ext σ w₁ e0) in He₂.
    destruct (sem_exp e0 (d₁, γ)) as [d₂|]; [|exact I].
    simpl in He₂. destruct He₂ as [w₂ [Heval₂ Hrel₂]].
    simpl. exists w₂. split; [exact (e_Let _ w₁ _ _ Heval₁ Heval₂) | exact Hrel₂].

  - (* APP v v0 *)
    simpl substExp. rewrite sem_exp_APP.
    pose proof (H _ _ H1) as Hfun. simpl rel_val in Hfun.
    destruct Hfun as [body [Hveq Hfun]].
    pose proof (H0 _ _ H1) as Harg.
    specialize (Hfun _ _ Harg).
    rewrite Hveq.
    (* Hfun has a different coercion path than the goal for the match
       discriminant, so rewrite can't match. Bridge via rel_exp: *)
    assert (Happ : rel_exp τ₂ (sem_val v γ (sem_val v0 γ))
                     (doubleSubstExp (substVal σ v0) (substVal σ v) body))
      by exact Hfun.
    rewrite Hveq in Happ.
    (* Now lift from doubleSubstExp to APP via e_App *)
    revert Happ. unfold rel_exp.
    destruct (sem_val v γ (sem_val v0 γ)); [|exact (fun _ => I)].
    intros [w [Heval Hrel]].
    exists w. split; [exact (e_App _ _ _ Heval) | exact Hrel].

  - (* FST v *)
    simpl.
    destruct (rel_val_prod_inv _ _ (H _ _ H0)) as [w₁ [w₂ [Hveq [Hr₁ Hr₂]]]].
    rewrite Hveq. simpl.
    exists w₁. split; [exact (e_Fst _ _) | exact Hr₁].

  - (* SND v *)
    simpl.
    destruct (rel_val_prod_inv _ _ (H _ _ H0)) as [w₁ [w₂ [Hveq [Hr₁ Hr₂]]]].
    rewrite Hveq. simpl.
    exists w₂. split; [exact (e_Snd _ _) | exact Hr₂].

  - (* OP op v v0 *)
    simpl.
    pose proof (H _ _ H1) as Hr₁. simpl rel_val in Hr₁.
    pose proof (H0 _ _ H1) as Hr₂. simpl rel_val in Hr₂.
    rewrite Hr₁, Hr₂.
    exists (NLIT (n (sem_val v γ) (sem_val v0 γ))).
    split; [exact (e_Op _ _ _) | reflexivity].

  - (* GT v v0 *)
    simpl.
    pose proof (H _ _ H1) as Hr₁. simpl rel_val in Hr₁.
    pose proof (H0 _ _ H1) as Hr₂. simpl rel_val in Hr₂.
    rewrite Hr₁, Hr₂.
    exists (BLIT (Nat.ltb (sem_val v0 γ) (sem_val v γ))).
    split; [exact (e_Gt _ _) | reflexivity].

  - (* IFB v e e0 *)
    simpl substExp. rewrite sem_exp_IFB.
    pose proof (H _ _ H2) as Hbool.
    revert Hbool. destruct (sem_val v γ : bool); intro Hbool;
      simpl rel_val in Hbool; rewrite Hbool.
    + specialize (H0 _ _ H2) as He₁.
      destruct (sem_exp e γ) as [d|]; [|exact I].
      simpl in He₁ |- *. destruct He₁ as [w [Heval Hrel]].
      exists w. split; [exact (e_IfTrue _ _ _ Heval) | exact Hrel].
    + specialize (H1 _ _ H2) as He₂.
      destruct (sem_exp e0 γ) as [d|]; [|exact I].
      simpl in He₂ |- *. destruct He₂ as [w [Heval Hrel]].
      exists w. split; [exact (e_IfFalse _ _ _ Heval) | exact Hrel].
Qed.

(* ================================================================== *)
(*   §4  Adequacy theorem                                              *)
(* ================================================================== *)
(*
    The adequacy theorem follows from the fundamental lemma applied at
    the empty environment.

    For a closed expression [e : CExp τ], we instantiate the fundamental
    lemma with [σ = empty, γ = tt].  The conclusion is:
      rel_exp τ (sem_exp e tt) (substExp empty e)
    Since [e] is closed, [substExp empty e = e] (by [sem_subst_id] at
    the semantic level — syntactically [substExp id e = e]).
    If [sem_exp e tt <> None], then [sem_exp e tt = Some d] for some [d],
    and the relation gives [∃ v, e ⇓ v].
*)

Theorem adequacy :
    forall {τ : Ty} (e : CExp τ),
      sem_exp e tt <> None -> e ⇓.
Proof.
  intros τ e Hne.
  destruct fundamental_lemma as [_ Hexp].
  assert (Henv : rel_env [] tt subst_id)
    by (intros τ' x; dependent destruction x).
  specialize (Hexp [] τ e subst_id tt Henv).
  rewrite substExp_id in Hexp.
  destruct (sem_exp e tt) as [d|]; [|contradiction].
  exact (rel_exp_some_converges d e Hexp).
Qed.


(* ================================================================== *)
(*   §5  Full correspondence                                          *)
(* ================================================================== *)

(*  The complete operational/denotational correspondence.
    Forward: [soundness] (from PCF_Soundness.v).
    Converse: [adequacy] (above).                                     *)

Corollary convergence_iff_defined :
    forall {τ : Ty} (e : CExp τ),
      e ⇓  <->  sem_exp e tt <> None.
Proof.
  intros τ e. split.
  - intros [v Hv]. rewrite (soundness e v Hv). discriminate.
  - exact (adequacy e).
Qed.

(*  The "easy" direction, restated for convenience. *)
Corollary convergence_implies_defined :
    forall {τ : Ty} (e : CExp τ),
      e ⇓  ->  sem_exp e tt <> None.
Proof.
  intros τ e [v Hv].
  rewrite (soundness e v Hv). discriminate.
Qed.
