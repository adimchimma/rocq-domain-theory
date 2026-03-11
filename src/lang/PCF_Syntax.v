(*  PCF_Syntax

    Phase 1: Syntax of PCFv, a call-by-value PCF with products.

    This is [src/lang/PCF_Syntax.v].

    No imports from DomainTheory are needed here — this file is purely
    syntactic and does not mention CPOs.  Semantic dependencies begin in
    [PCF_Denotational.v].

    Imports (Stdlib only):
      Stdlib.Lists.List — [list], [nth_error]

    Summary
    =======
    We formalize PCFv following Benton and Kennedy's strongly-typed term
    representation.  The key design choice is that every syntactic object
    is indexed by its typing context [Γ : Env] and its type [τ : Ty],
    guaranteeing well-typedness by construction.  There are no separate
    typing judgments, no proof objects inside terms, and no need to prove
    typing-uniqueness lemmas.

    The language is call-by-value with products, integers, booleans, and
    general recursion.  Terms are in _administrative normal form_ (ANF):
    the argument to every function call must already be a value, and
    intermediate computations are sequenced explicitly by [LET].

    Types:
        τ ::= Nat | Bool | τ₁ → τ₂ | τ₁ × τ₂

    Values (already evaluated):
        v ::= n              (nat literal)
            | b              (bool literal)
            | x              (variable)
            | fix (τ₁,τ₂, e) (general recursion: self-referential λ)
            | ⟨v₁, v₂⟩       (pair)

    Expressions (may diverge, produce a value):
        e ::= val v          (promote a value to an expression)
            | let x = e₁ in e₂     (sequential composition)
            | v₁ v₂                (function application)
            | fst v | snd v        (projections)
            | op v₁ v₂             (arithmetic: addition, etc.)
            | v₁ > v₂              (comparison)
            | if v then e₁ else e₂ (boolean conditional)

    Binders:
      - [fix τ₁ τ₂ e] binds two variables in [e]:
        the function argument (of type τ₁) and the function itself (of
        type τ₁ → τ₂), so [e] is typed in [τ₁ :: (τ₁ → τ₂) :: Γ].
      - [let x = e₁ in e₂] binds one variable in [e₂]: [e₂] is typed
        in [τ₁ :: Γ] where [τ₁] is the type of [e₁].

    Binding representation:
      De Bruijn indices, enforced by [Var Γ τ] — a proof that type [τ]
      lives at some position in the context [Γ].  Variables are never
      raw [nat]s; they are typed membership witnesses.

    Substitutions:
      A substitution [Subst Γ Γ'] is a context-indexed family of value
      maps [∀ τ, Var Γ τ → Value Γ' τ].  Following Benton-Kennedy, we
      bootstrap via _renamings_ (Var-to-Var maps) to avoid the need for
      a separate shift operator.

    Contents:
    - §1  Types and environments
    - §2  Variables — typed de Bruijn indices
    - §3  Terms — [Value] and [Exp] (mutually inductive, ANF)
    - §4  Closed terms
    - §5  Renamings — context maps [Var Γ τ → Var Γ' τ]
    - §6  Substitutions — context maps [Var Γ τ → Value Γ' τ]
    - §7  Single and double substitution — computation rules

    Phase coverage:
      Phase 1 — all sections
      Used by [PCF_Operational.v], [PCF_Denotational.v]

    References:
      Benton & Kennedy, "Some Domain Theory and Denotational Semantics
      in Rocq" (2009), §3.
*)

From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.
Import ListNotations.


(* ================================================================== *)
(*   §1  Types and environments                                        *)
(* ================================================================== *)
(*
    PCFv types.  [Nat] and [Bool] are the base types; [Arrow] and [Prod]
    are the two type constructors.  We write [τ₁ →ₜ τ₂] and [τ₁ ×ₜ τ₂]
    for the arrow and product to avoid clashing with Coq's own [->] and [*].
*)

Inductive Ty : Type :=
  | Nat  : Ty
  | Bool : Ty
  | Arrow (τ₁ τ₂ : Ty) : Ty
  | Prod  (τ₁ τ₂ : Ty) : Ty.

Notation "τ₁ →ₜ τ₂" := (Arrow τ₁ τ₂) (at level 55, right associativity).
Notation "τ₁ ×ₜ τ₂" := (Prod τ₁ τ₂) (at level 50, left associativity).

(*
    A typing environment is a list of types.  The head of the list is
    the most-recently-bound variable (de Bruijn convention: index 0 is
    the innermost binder).
*)
Definition Env : Type := list Ty.

(* ================================================================== *)
(*   §2  Variables — typed de Bruijn indices                          *)
(* ================================================================== *)
(*
    [Var Γ τ] is the type of well-typed de Bruijn indices into [Γ].
    A value of type [Var Γ τ] is simultaneously:
      - a proof that [τ] appears somewhere in [Γ], and
      - a pointer to the position where it appears.

    [ZVAR] is index 0 (the head of the context).
    [SVAR v] is index [1 + i] where [v : Var Γ τ] has index [i].

    This is the standard intrinsic representation from Benton-Kennedy.
*)

Inductive Var : Env -> Ty -> Type :=
  | ZVAR : forall {Γ : Env} {τ : Ty},
      Var (τ :: Γ) τ
  | SVAR : forall {Γ : Env} {τ τ' : Ty},
      Var Γ τ -> Var (τ' :: Γ) τ.

Arguments ZVAR {Γ τ}.
Arguments SVAR {Γ τ τ'} v.


(* ================================================================== *)
(*   §3  Terms — [Value] and [Exp]                                    *)
(* ================================================================== *)
(*
    Values and expressions are mutually defined.  Every constructor is
    indexed by the typing context [Γ] and the type [τ], so every term
    in the AST is well-typed by construction.

    Values are in _weak head normal form_ and do not require further
    evaluation:
      - integer and boolean literals,
      - variables,
      - [FIX]: the only binder for recursion (λ with self-reference),
      - [PAIR v₁ v₂]: a pair of values.
    
    [weak head normal form] (https://stackoverflow.com/questions/6872898/what-is-weak-head-normal-form)

    Expressions may diverge and represent computations that eventually
    produce a value (or fail to terminate):
      - [VAL v]: promote a value to an expression (the trivial computation),
      - [LET e₁ e₂]: evaluate [e₁], bind the result, evaluate [e₂],
      - [APP v₁ v₂]: apply a function value to an argument value,
      - [FST v], [SND v]: projections from a pair,
      - [OP op v₁ v₂]: binary arithmetic operation (nat → nat → nat),
      - [GT v₁ v₂]: comparison (nat → nat → bool),
      - [IFB v e₁ e₂]: boolean branch.

    The type [op_type] for arithmetic is (nat -> nat -> nat) so that
    the user can pass in any concrete operation (add, mul, etc.) without
    fixing a particular set of built-ins.  This keeps the syntax small
    and the denotational semantics clean.

    Note on FIX: we follow Benton-Kennedy exactly.
      [FIX τ₁ τ₂ e] represents [fix f(x : τ₁) : τ₂ = e]
      where inside [e]:
        - index 0 (ZVAR) is the argument [x : τ₁]
        - index 1 (SVAR ZVAR) is the function itself [f : τ₁ →ₜ τ₂]
      Hence the body [e] is typed in the context [τ₁ :: (τ₁ →ₜ τ₂) :: Γ].
*)

Inductive Value : Env -> Ty -> Type :=
  (*  Literals  *)
  | NLIT  : forall {Γ},
      nat -> Value Γ Nat
  | BLIT  : forall {Γ},
      bool -> Value Γ Bool
  (*  Variable  *)
  | VAR   : forall {Γ τ},
      Var Γ τ -> Value Γ τ
  (*  General recursion: fix f(x:τ₁):τ₂ = e
      The body e is typed in [τ₁ :: (τ₁ →ₜ τ₂) :: Γ]:
        index 0 = argument x : τ₁
        index 1 = self f : τ₁ →ₜ τ₂               *)
  | FIX   : forall {Γ} (τ₁ τ₂ : Ty),
      Exp (τ₁ :: (τ₁ →ₜ τ₂) :: Γ) τ₂ -> Value Γ (τ₁ →ₜ τ₂)
  (*  Pair  *)
  | PAIR  : forall {Γ τ₁ τ₂},
      Value Γ τ₁ -> Value Γ τ₂ -> Value Γ (τ₁ ×ₜ τ₂)

with Exp : Env -> Ty -> Type :=
  (*  Promote a value to an expression  *)
  | VAL   : forall {Γ τ},
      Value Γ τ -> Exp Γ τ
  (*  Sequential composition (LET in ANF)  *)
  | LET   : forall {Γ τ₁ τ₂},
      Exp Γ τ₁ -> Exp (τ₁ :: Γ) τ₂ -> Exp Γ τ₂
  (*  Function application (both parts must be values)  *)
  | APP   : forall {Γ τ₁ τ₂},
      Value Γ (τ₁ →ₜ τ₂) -> Value Γ τ₁ -> Exp Γ τ₂
  (*  Projections  *)
  | FST   : forall {Γ τ₁ τ₂},
      Value Γ (τ₁ ×ₜ τ₂) -> Exp Γ τ₁
  | SND   : forall {Γ τ₁ τ₂},
      Value Γ (τ₁ ×ₜ τ₂) -> Exp Γ τ₂
  (*  Arithmetic: binary nat operation  *)
  | OP    : forall {Γ},
      (nat -> nat -> nat) -> Value Γ Nat -> Value Γ Nat -> Exp Γ Nat
  (*  Comparison: n > m  *)
  | GT    : forall {Γ},
      Value Γ Nat -> Value Γ Nat -> Exp Γ Bool
  (*  Boolean conditional  *)
  | IFB   : forall {Γ τ},
      Value Γ Bool -> Exp Γ τ -> Exp Γ τ -> Exp Γ τ.

Arguments NLIT  {Γ} n.
Arguments BLIT  {Γ} b.
Arguments VAR   {Γ τ} v.
Arguments FIX   {Γ} τ₁ τ₂ e.
Arguments PAIR  {Γ τ₁ τ₂} v₁ v₂.

Arguments VAL   {Γ τ} v.
Arguments LET   {Γ τ₁ τ₂} e₁ e₂.
Arguments APP   {Γ τ₁ τ₂} v₁ v₂.
Arguments FST   {Γ τ₁ τ₂} v.
Arguments SND   {Γ τ₁ τ₂} v.
Arguments OP    {Γ} op v₁ v₂.
Arguments GT    {Γ} v₁ v₂.
Arguments IFB   {Γ τ} v e₁ e₂.


(* ================================================================== *)
(*   §4  Closed terms                                                 *)
(* ================================================================== *)
(*
    A _closed_ term has an empty typing context.  These are the terms
    that the operational semantics evaluates.
*)

Definition CValue (τ : Ty) : Type := Value [] τ.
Definition CExp   (τ : Ty) : Type := Exp   [] τ.


(* ================================================================== *)
(*   §5  Renamings                                                    *)
(* ================================================================== *)
(*
    A _renaming_ from [Γ] to [Γ'] is a typed variable map:
        [Ren Γ Γ' = ∀ τ, Var Γ τ → Var Γ' τ]

    Renamings are used to define the _weakening_ (shift) operation on
    terms, which is the main technical device needed to bootstrap
    substitution.  By defining renaming-application before substitution-
    application, we avoid having to define and verify a shift lemma at
    the level of values.

    This is the approach taken in Benton-Kennedy and in the PLFA-style
    treatment of intrinsic de Bruijn syntax.
*)

Definition Ren (Γ Γ' : Env) : Type :=
  forall τ, Var Γ τ -> Var Γ' τ.

(*  The identity renaming  *)
Definition ren_id {Γ : Env} : Ren Γ Γ :=
  fun _ v => v.

(*  Composition of renamings  *)
Definition ren_comp {Γ Γ' Γ'' : Env}
    (ρ₂ : Ren Γ' Γ'') (ρ₁ : Ren Γ Γ') : Ren Γ Γ'' :=
  fun τ v => ρ₂ τ (ρ₁ τ v).

(*
    [var_case] is a computational case analysis on de Bruijn indices
    that avoids the opaque [JMeq_eq] axiom introduced by [dependent
    destruction].  All definitions that case-split on a [Var (τ :: Γ)]
    ([ren_ext], [subst_ext], [single_subst], [double_subst]) use this
    combinator so that their computation rules hold definitionally.
*)
Definition var_case {Γ τ} {P : Ty -> Type}
    (hz : P τ) (hs : forall σ, Var Γ σ -> P σ)
    : forall σ, Var (τ :: Γ) σ -> P σ :=
  fun σ (x : Var (τ :: Γ) σ) =>
    match x in Var ctx σ' return
          match ctx with
          | []       => P σ'
          | τ₀ :: Γ₀ => P τ₀ -> (forall σ, Var Γ₀ σ -> P σ) -> P σ'
          end
    with
    | ZVAR   => fun z _  => z
    | SVAR y => fun _ s  => s _ y
    end hz hs.

(*
    _Extension_ of a renaming under a binder.
    If [ρ : Ren Γ Γ'] then [ren_ext ρ : Ren (τ :: Γ) (τ :: Γ')].
    The new head variable [ZVAR] maps to itself; all other variables
    are shifted by one and then renamed by [ρ].
*)
Definition ren_ext {Γ Γ' : Env} {τ : Ty} (ρ : Ren Γ Γ') :
    Ren (τ :: Γ) (τ :: Γ') :=
  var_case ZVAR (fun σ y => SVAR (ρ σ y)).

(*
    _Weakening_: the canonical renaming from [Γ] into [τ :: Γ] that
    shifts every variable by one, making room for the new head binding.
*)
Definition ren_wk {Γ : Env} {τ : Ty} : Ren Γ (τ :: Γ) :=
  fun _ v => SVAR v.

(*
    Apply a renaming to a value or expression.  These two functions are
    mutually recursive, following the mutual induction on [Value]/[Exp].
*)
Fixpoint renVal {Γ Γ' : Env} (ρ : Ren Γ Γ') {τ : Ty}
    (v : Value Γ τ) {struct v} : Value Γ' τ :=
  match v in Value G T return Ren G Γ' -> Value Γ' T with
  | NLIT n       => fun _  => NLIT n
  | BLIT b       => fun _  => BLIT b
  | VAR  x       => fun ρ  => VAR (ρ _ x)
  | FIX  τ₁ τ₂ e => fun ρ  => FIX τ₁ τ₂ (renExp (ren_ext (ren_ext ρ)) e)
  | PAIR v₁ v₂   => fun ρ  => PAIR (renVal ρ v₁) (renVal ρ v₂)
  end ρ

with renExp {Γ Γ' : Env} (ρ : Ren Γ Γ') {τ : Ty}
    (e : Exp Γ τ) {struct e} : Exp Γ' τ :=
  match e in Exp G T return Ren G Γ' -> Exp Γ' T with
  | VAL  v         => fun ρ  => VAL  (renVal ρ v)
  | LET  e₁ e₂     => fun ρ  => LET  (renExp ρ e₁) (renExp (ren_ext ρ) e₂)
  | APP  v₁ v₂     => fun ρ  => APP  (renVal ρ v₁) (renVal ρ v₂)
  | FST  v         => fun ρ  => FST  (renVal ρ v)
  | SND  v         => fun ρ  => SND  (renVal ρ v)
  | OP   op v₁ v₂  => fun ρ  => OP op (renVal ρ v₁) (renVal ρ v₂)
  | GT   v₁ v₂     => fun ρ  => GT   (renVal ρ v₁) (renVal ρ v₂)
  | IFB  v e₁ e₂   => fun ρ  => IFB (renVal ρ v) (renExp ρ e₁) (renExp ρ e₂)
  end ρ.

(*
    Weakening: embed a term from [Γ] into [τ :: Γ] by shifting all
    variables. This is the primitive operation that substitution needs.
*)
Definition wkVal {Γ : Env} {τ σ : Ty} (v : Value Γ τ) : Value (σ :: Γ) τ :=
  renVal ren_wk v.


(* ================================================================== *)
(*   §6  Substitutions                                                *)
(* ================================================================== *)
(*
    A _substitution_ from [Γ] to [Γ'] is a typed value map:
        [Subst Γ Γ' = ∀ τ, Var Γ τ → Value Γ' τ]

    Intuitively, a substitution maps each variable in [Γ] to a [Value]
    typed in [Γ'].

    Extension under a binder uses the same [ZVAR]/[SVAR] case split as
    for renamings, but now the tail case must _weaken_ the value produced
    by the substitution (since we are pushing it under an extra binder).
    This is exactly where the bootstrapped [wkVal] is needed.
*)

Definition Subst (Γ Γ' : Env) : Type :=
  forall τ, Var Γ τ -> Value Γ' τ.

(*  The identity substitution: map each variable to its [VAR] *)
Definition subst_id {Γ : Env} : Subst Γ Γ :=
  fun _ v => VAR v.

(*
    Extend a substitution under a new binder.
    [subst_ext σ : Subst (τ :: Γ) (τ :: Γ')]
      maps ZVAR   ↦ VAR ZVAR   (the new head variable, kept as-is)
      maps SVAR v ↦ wkVal (σ v) (the old variables, weakened by one)
*)
Definition subst_ext {Γ Γ' : Env} {τ : Ty} (σ : Subst Γ Γ') :
    Subst (τ :: Γ) (τ :: Γ') :=
  var_case (VAR ZVAR) (fun ρ y => wkVal (σ ρ y)).

(*
    Apply a substitution to a value or expression.  Again, these are
    mutually recursive.

    For FIX, we must extend the substitution _twice_ (for the two
    newly-bound variables: the argument and the self-reference).
*)
Fixpoint substVal {Γ Γ' : Env} (σ : Subst Γ Γ') {τ : Ty}
    (v : Value Γ τ) {struct v} : Value Γ' τ :=
  match v in Value G T return Subst G Γ' -> Value Γ' T with
  | NLIT n        => fun _  => NLIT n
  | BLIT b        => fun _  => BLIT b
  | VAR  x        => fun σ  => σ _ x
  | FIX  τ₁ τ₂ e  => fun σ  => FIX τ₁ τ₂ (substExp (subst_ext (subst_ext σ)) e)
  | PAIR v₁ v₂    => fun σ  => PAIR (substVal σ v₁) (substVal σ v₂)
  end σ

with substExp {Γ Γ' : Env} (σ : Subst Γ Γ') {τ : Ty}
    (e : Exp Γ τ) {struct e} : Exp Γ' τ :=
  match e in Exp G T return Subst G Γ' -> Exp Γ' T with
  | VAL  v         => fun σ  => VAL  (substVal σ v)
  | LET  e₁ e₂    => fun σ  => LET  (substExp σ e₁) (substExp (subst_ext σ) e₂)
  | APP  v₁ v₂    => fun σ  => APP  (substVal σ v₁) (substVal σ v₂)
  | FST  v         => fun σ  => FST  (substVal σ v)
  | SND  v         => fun σ  => SND  (substVal σ v)
  | OP   op v₁ v₂  => fun σ  => OP op (substVal σ v₁) (substVal σ v₂)
  | GT   v₁ v₂    => fun σ  => GT   (substVal σ v₁) (substVal σ v₂)
  | IFB  v e₁ e₂  => fun σ  => IFB  (substVal σ v) (substExp σ e₁) (substExp σ e₂)
  end σ.


(* ================================================================== *)
(*   §7  Single and double substitution                               *)
(* ================================================================== *)
(*
    The operational semantics needs two special-purpose substitution
    functions:

    [singleSubst v e]: substitute [v] for [ZVAR] in [e], where
      [e : Exp (τ₁ :: Γ) τ₂] and [v : Value Γ τ₁].
      Used for the [LET] evaluation rule:
        [let x = v in e ⇓ w]  ↔  [e[v/x] ⇓ w]

    [doubleSubst varg vfun e]: substitute [varg] for [ZVAR] and
      [vfun] for [SVAR ZVAR] in [e], where
      [e : Exp (τ₁ :: (τ₁ →ₜ τ₂) :: Γ) τ₂].
      Used for the [APP/FIX] evaluation rule:
        [(fix f(x) = e) varg ⇓ w]  ↔  [e[varg/x, fix.../f] ⇓ w]

    Both are defined by constructing the appropriate [Subst].
*)

(*
    The substitution that maps [ZVAR ↦ v] and leaves all other variables
    shifted down by one (unchanged in the outer context).

    [single_subst], [double_subst], [ren_ext], and [subst_ext] are all
    defined via [var_case] (see §4), ensuring their computation rules
    hold _definitionally_:
        [single_subst v τ ZVAR        ≡ v        ]
        [single_subst v σ (SVAR x)    ≡ VAR x    ]
        [double_subst varg vfun _ ZVAR           ≡ varg   ]
        [double_subst varg vfun _ (SVAR ZVAR)    ≡ vfun   ]
        [double_subst varg vfun _ (SVAR (SVAR x)) ≡ VAR x ]
*)
Definition single_subst {Γ : Env} {τ : Ty} (v : Value Γ τ) :
    Subst (τ :: Γ) Γ :=
  var_case v (fun σ x => VAR x).

(* Substitute [v] for variable 0 in an expression. *)
Definition singleSubstExp {Γ : Env} {τ₁ τ₂ : Ty}
    (v : Value Γ τ₁) (e : Exp (τ₁ :: Γ) τ₂) : Exp Γ τ₂ :=
  substExp (single_subst v) e.

(*
    The substitution for the FIX reduction rule.
    Maps:
      ZVAR         ↦ varg        (the argument, x)
      SVAR ZVAR    ↦ vfun        (the function itself, f)
      SVAR (SVAR w) ↦ VAR w     (outer variables, unchanged)
*)
Definition double_subst {Γ : Env} {τ₁ τ₂ : Ty}
    (varg : Value Γ τ₁) (vfun : Value Γ (τ₁ →ₜ τ₂)) :
    Subst (τ₁ :: (τ₁ →ₜ τ₂) :: Γ) Γ :=
  var_case varg (var_case vfun (fun σ x => VAR x)).

(*
    Apply the double substitution to the body of a FIX.
*)
Definition doubleSubstExp {Γ : Env} {τ₁ τ₂ : Ty}
    (varg : Value Γ τ₁) (vfun : Value Γ (τ₁ →ₜ τ₂))
    (e : Exp (τ₁ :: (τ₁ →ₜ τ₂) :: Γ) τ₂) : Exp Γ τ₂ :=
  substExp (double_subst varg vfun) e.


(* ================================================================== *)
(*   §8  Substitution metatheory                                      *)
(* ================================================================== *)
(*
    This section contains the standard sigma-calculus lemmas for
    intrinsic de Bruijn representations:

    §8a  Extensionality — renamings and substitutions that agree
         pointwise produce the same result.
    §8b  Renaming composition — consecutive renamings fuse.
    §8c  Substitution–renaming interaction — substituting after
         renaming, or renaming after substituting, can each be
         expressed as a single substitution.
    §8d  Substitution composition (fusion) — consecutive substitutions
         fuse into a single substitution.

    All proofs are by mutual induction on the [Value]/[Exp] structure.
    Each "binder case" ([FIX], [LET]) reduces to the induction hypothesis
    plus extensionality (to align the extended substitution/renaming).

    Strategy: In [Lemma ... with ...] blocks, Rocq makes all implicit
    binders explicit.  We therefore use [intro term; destruct term]
    (or just [destruct term] since it auto-intros dependencies), then
    manually [intros] the remaining parameters.  This mirrors the
    approach used in [PCF_Denotational.v].
*)


(* ------------------------------------------------------------------ *)
(*   §8a  Extensionality                                               *)
(* ------------------------------------------------------------------ *)

Lemma renVal_ext : forall {Γ Γ' : Env} {τ : Ty}
    (v : Value Γ τ) (ρ₁ ρ₂ : Ren Γ Γ'),
    (forall σ (x : Var Γ σ), ρ₁ σ x = ρ₂ σ x) ->
    renVal ρ₁ v = renVal ρ₂ v
with renExp_ext : forall {Γ Γ' : Env} {τ : Ty}
    (e : Exp Γ τ) (ρ₁ ρ₂ : Ren Γ Γ'),
    (forall σ (x : Var Γ σ), ρ₁ σ x = ρ₂ σ x) ->
    renExp ρ₁ e = renExp ρ₂ e.
Proof.
  { destruct v; intros ? ? Hext; simpl.
    - reflexivity.
    - reflexivity.
    - f_equal. apply Hext.
    - (* FIX *) f_equal. apply renExp_ext.
      intros σ x; dependent destruction x; [reflexivity|]; simpl.
      dependent destruction x; simpl; [reflexivity | do 2 f_equal; apply Hext].
    - (* PAIR *) f_equal; apply renVal_ext; exact Hext. }
  { destruct e; intros ? ? Hext; simpl.
    - f_equal. apply renVal_ext. exact Hext.
    - (* LET *) f_equal.
      + apply renExp_ext. exact Hext.
      + apply renExp_ext. intros σ x; dependent destruction x;
          [reflexivity | simpl; f_equal; apply Hext].
    - f_equal; apply renVal_ext; exact Hext.
    - f_equal. apply renVal_ext. exact Hext.
    - f_equal. apply renVal_ext. exact Hext.
    - f_equal; apply renVal_ext; exact Hext.
    - f_equal; apply renVal_ext; exact Hext.
    - f_equal; [apply renVal_ext | apply renExp_ext | apply renExp_ext]; exact Hext. }
Qed.

Lemma substVal_ext : forall {Γ Γ' : Env} {τ : Ty}
    (v : Value Γ τ) (σ₁ σ₂ : Subst Γ Γ'),
    (forall ρ (x : Var Γ ρ), σ₁ ρ x = σ₂ ρ x) ->
    substVal σ₁ v = substVal σ₂ v
with substExp_ext : forall {Γ Γ' : Env} {τ : Ty}
    (e : Exp Γ τ) (σ₁ σ₂ : Subst Γ Γ'),
    (forall ρ (x : Var Γ ρ), σ₁ ρ x = σ₂ ρ x) ->
    substExp σ₁ e = substExp σ₂ e.
Proof.
  { destruct v; intros ? ? Hext; simpl.
    - reflexivity.
    - reflexivity.
    - apply Hext.
    - (* FIX *) f_equal. apply substExp_ext.
      intros ρ x; dependent destruction x; [reflexivity|]; simpl.
      dependent destruction x; simpl;
        [f_equal; apply Hext | unfold wkVal; f_equal; f_equal; apply Hext].
    - (* PAIR *) f_equal; apply substVal_ext; exact Hext. }
  { destruct e; intros ? ? Hext; simpl.
    - f_equal. apply substVal_ext. exact Hext.
    - (* LET *) f_equal.
      + apply substExp_ext. exact Hext.
      + apply substExp_ext. intros ρ x; dependent destruction x; [reflexivity|]; simpl.
        unfold wkVal. f_equal. apply Hext.
    - f_equal; apply substVal_ext; exact Hext.
    - f_equal. apply substVal_ext. exact Hext.
    - f_equal. apply substVal_ext. exact Hext.
    - f_equal; apply substVal_ext; exact Hext.
    - f_equal; apply substVal_ext; exact Hext.
    - (* IFB *) f_equal;
        [apply substVal_ext | apply substExp_ext | apply substExp_ext]; exact Hext. }
Qed.


(* ------------------------------------------------------------------ *)
(*   §8b  Renaming composition                                        *)
(* ------------------------------------------------------------------ *)

Lemma renVal_comp : forall {Γ Γ' Γ'' : Env} {τ : Ty}
    (v : Value Γ τ) (ρ₂ : Ren Γ' Γ'') (ρ₁ : Ren Γ Γ'),
    renVal ρ₂ (renVal ρ₁ v) = renVal (ren_comp ρ₂ ρ₁) v
with renExp_comp : forall {Γ Γ' Γ'' : Env} {τ : Ty}
    (e : Exp Γ τ) (ρ₂ : Ren Γ' Γ'') (ρ₁ : Ren Γ Γ'),
    renExp ρ₂ (renExp ρ₁ e) = renExp (ren_comp ρ₂ ρ₁) e.
Proof.
  { destruct v; intros ? ?; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* FIX *) f_equal. rewrite renExp_comp. apply renExp_ext.
      intros σ x; dependent destruction x; [reflexivity|]; simpl.
      dependent destruction x; simpl; reflexivity.
    - (* PAIR *) f_equal; apply renVal_comp. }
  { destruct e; intros ? ?; simpl.
    - f_equal. apply renVal_comp.
    - (* LET *) f_equal.
      + apply renExp_comp.
      + rewrite renExp_comp. apply renExp_ext.
        intros σ x; dependent destruction x; [reflexivity | simpl; reflexivity].
    - f_equal; apply renVal_comp.
    - f_equal. apply renVal_comp.
    - f_equal. apply renVal_comp.
    - f_equal; apply renVal_comp.
    - f_equal; apply renVal_comp.
    - f_equal; [apply renVal_comp | apply renExp_comp | apply renExp_comp]. }
Qed.


(* ------------------------------------------------------------------ *)
(*   §8c  Substitution–renaming interaction                           *)
(* ------------------------------------------------------------------ *)
(*
    [substVal_renVal]: substitution after renaming.
      substVal σ (renVal ρ v) = substVal (fun τ x => σ τ (ρ τ x)) v

    [renVal_substVal]: renaming after substitution.
      renVal ρ (substVal σ v) = substVal (fun τ x => renVal ρ (σ τ x)) v
*)

Lemma substVal_renVal : forall {Γ Γ' Γ'' : Env} {τ : Ty}
    (v : Value Γ τ) (σ : Subst Γ' Γ'') (ρ : Ren Γ Γ'),
    substVal σ (renVal ρ v) = substVal (fun τ x => σ τ (ρ τ x)) v
with substExp_renExp : forall {Γ Γ' Γ'' : Env} {τ : Ty}
    (e : Exp Γ τ) (σ : Subst Γ' Γ'') (ρ : Ren Γ Γ'),
    substExp σ (renExp ρ e) = substExp (fun τ x => σ τ (ρ τ x)) e.
Proof.
  { destruct v; intros ? ?; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* FIX *) f_equal. rewrite substExp_renExp. apply substExp_ext.
      intros ρ' x; dependent destruction x; [reflexivity|]; simpl.
      dependent destruction x; simpl; reflexivity.
    - (* PAIR *) f_equal; apply substVal_renVal. }
  { destruct e; intros ? ?; simpl.
    - f_equal. apply substVal_renVal.
    - (* LET *) f_equal.
      + apply substExp_renExp.
      + rewrite substExp_renExp. apply substExp_ext.
        intros ρ' x; dependent destruction x; [reflexivity|]; simpl.
        reflexivity.
    - f_equal; apply substVal_renVal.
    - f_equal. apply substVal_renVal.
    - f_equal. apply substVal_renVal.
    - f_equal; apply substVal_renVal.
    - f_equal; apply substVal_renVal.
    - f_equal; [apply substVal_renVal | apply substExp_renExp | apply substExp_renExp]. }
Qed.

Lemma renVal_substVal : forall {Γ Γ' Γ'' : Env} {τ : Ty}
    (v : Value Γ τ) (ρ : Ren Γ' Γ'') (σ : Subst Γ Γ'),
    renVal ρ (substVal σ v) = substVal (fun τ x => renVal ρ (σ τ x)) v
with renExp_substExp : forall {Γ Γ' Γ'' : Env} {τ : Ty}
    (e : Exp Γ τ) (ρ : Ren Γ' Γ'') (σ : Subst Γ Γ'),
    renExp ρ (substExp σ e) = substExp (fun τ x => renVal ρ (σ τ x)) e.
Proof.
  { destruct v; intros ? ?; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* FIX *) f_equal. rewrite renExp_substExp. apply substExp_ext.
      intros ρ' x; dependent destruction x; [reflexivity|]; simpl.
      dependent destruction x; simpl;
        [reflexivity | unfold wkVal; rewrite !renVal_comp; apply renVal_ext;
         intros ? ?; reflexivity].
    - (* PAIR *) f_equal; apply renVal_substVal. }
  { destruct e; intros ? ?; simpl.
    - f_equal. apply renVal_substVal.
    - (* LET *) f_equal.
      + apply renExp_substExp.
      + rewrite renExp_substExp. apply substExp_ext.
        intros ρ' x; dependent destruction x; [reflexivity|]; simpl.
        unfold wkVal. rewrite !renVal_comp.
        apply renVal_ext. intros ? ?. reflexivity.
    - f_equal; apply renVal_substVal.
    - f_equal. apply renVal_substVal.
    - f_equal. apply renVal_substVal.
    - f_equal; apply renVal_substVal.
    - f_equal; apply renVal_substVal.
    - f_equal; [apply renVal_substVal | apply renExp_substExp | apply renExp_substExp]. }
Qed.


(* ------------------------------------------------------------------ *)
(*   §8d  Substitution composition (fusion)                           *)
(* ------------------------------------------------------------------ *)
(*
    substVal σ₂ (substVal σ₁ v) = substVal (fun τ x => substVal σ₂ (σ₁ τ x)) v
    substExp σ₂ (substExp σ₁ e) = substExp (fun τ x => substVal σ₂ (σ₁ τ x)) e
*)

Lemma substVal_comp : forall {Γ Γ' Γ'' : Env} {τ : Ty}
    (v : Value Γ τ) (σ₂ : Subst Γ' Γ'') (σ₁ : Subst Γ Γ'),
    substVal σ₂ (substVal σ₁ v) = substVal (fun τ x => substVal σ₂ (σ₁ τ x)) v
with substExp_comp : forall {Γ Γ' Γ'' : Env} {τ : Ty}
    (e : Exp Γ τ) (σ₂ : Subst Γ' Γ'') (σ₁ : Subst Γ Γ'),
    substExp σ₂ (substExp σ₁ e) = substExp (fun τ x => substVal σ₂ (σ₁ τ x)) e.
Proof.
  { destruct v; intros ? ?; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* FIX *) f_equal. rewrite substExp_comp. apply substExp_ext.
      intros ρ x; dependent destruction x; [reflexivity|]; simpl.
      dependent destruction x; simpl;
        [reflexivity | unfold wkVal; rewrite !substVal_renVal, !renVal_substVal;
         apply substVal_ext; intros ? ?; simpl; reflexivity].
    - (* PAIR *) f_equal; apply substVal_comp. }
  { destruct e; intros ? ?; simpl.
    - f_equal. apply substVal_comp.
    - (* LET *) f_equal.
      + apply substExp_comp.
      + rewrite substExp_comp. apply substExp_ext.
        intros ρ x; dependent destruction x; [reflexivity|]; simpl.
        unfold wkVal. rewrite !substVal_renVal, !renVal_substVal.
        apply substVal_ext. intros ? ?. simpl. reflexivity.
    - f_equal; apply substVal_comp.
    - f_equal. apply substVal_comp.
    - f_equal. apply substVal_comp.
    - f_equal; apply substVal_comp.
    - f_equal; apply substVal_comp.
    - f_equal; [apply substVal_comp | apply substExp_comp | apply substExp_comp]. }
Qed.


(* ------------------------------------------------------------------ *)
(*   §8e  Identity substitution                                       *)
(* ------------------------------------------------------------------ *)

Lemma substVal_id : forall {Γ : Env} {τ : Ty}
    (v : Value Γ τ),
    substVal subst_id v = v
with substExp_id : forall {Γ : Env} {τ : Ty}
    (e : Exp Γ τ),
    substExp subst_id e = e.
Proof.
  { destruct v; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* FIX *) f_equal. rewrite <- (substExp_id _ _ e) at 2.
      apply substExp_ext.
      intros τ' x; dependent destruction x; [reflexivity|]; simpl.
      dependent destruction x; reflexivity.
    - (* PAIR *) f_equal; apply substVal_id. }
  { destruct e; simpl.
    - f_equal. apply substVal_id.
    - (* LET *) f_equal.
      + apply substExp_id.
      + rewrite <- (substExp_id _ _ e2) at 2.
        apply substExp_ext.
        intros τ' x; dependent destruction x; [reflexivity | simpl; reflexivity].
    - f_equal; apply substVal_id.
    - f_equal. apply substVal_id.
    - f_equal. apply substVal_id.
    - f_equal; apply substVal_id.
    - f_equal; apply substVal_id.
    - f_equal; [apply substVal_id | apply substExp_id | apply substExp_id]. }
Qed.


(* ================================================================== *)
(*   Derived notations and sanity checks                              *)
(* ================================================================== *)
(*
    A few derived variable notations for readability in examples.
    [var0], [var1], [var2] are the first three de Bruijn indices.
*)

Definition var0 {Γ : Env} {τ : Ty} : Value (τ :: Γ) τ :=
  VAR ZVAR.

Definition var1 {Γ : Env} {τ τ' : Ty} : Value (τ' :: τ :: Γ) τ :=
  VAR (SVAR ZVAR).

Definition var2 {Γ : Env} {τ τ' τ'' : Ty} : Value (τ'' :: τ' :: τ :: Γ) τ :=
  VAR (SVAR (SVAR ZVAR)).


(*
    Example: the closed term [add := fix f(n) = n] (identity on Nat),
    as a sanity check that the types work out.
    We use [VAL var0] so the body just returns the argument.
*)
Example identity_nat : CValue (Nat →ₜ Nat) :=
  FIX Nat Nat (VAL var0).

(*
    Example: the closed expression [add 3 5] using a primitive OP.
    Here we write it as [OP plus (NLIT 3) (NLIT 5)], which has type
    [CExp Nat].
*)
Example add_3_5 : CExp Nat :=
  OP Nat.add (NLIT 3) (NLIT 5).

(*
    Example: a closed [LET] expression:
      let x = OP plus (NLIT 1) (NLIT 2) in
      VAL x
    Both the bound expression and the body must type-check.
*)
Example let_example : CExp Nat :=
  LET (OP Nat.add (NLIT 1) (NLIT 2)) (VAL var0).