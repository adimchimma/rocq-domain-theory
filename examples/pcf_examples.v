(*  pcf_examples -- Worked examples: PCF programs and their semantics.

    This file demonstrates the full stack of the PCF formalisation:
    writing programs, proving operational evaluation, computing
    denotational semantics, and applying soundness and adequacy.

    PCF (Programming Computable Functions) is a typed lambda calculus
    with natural numbers, booleans, products, and general recursion
    via [FIX].  Terms are in A-normal form with explicit [LET] for
    sequencing.  The semantics uses call-by-value evaluation.

    Contents:
    - §1  Base expressions -- literals, arithmetic, comparison, if
    - §2  Function application -- identity, constant, double
    - §3  Denotational semantics -- computing [sem_cexp] for each
    - §4  Soundness -- relating evaluation to denotation
    - §5  Adequacy -- convergence iff denotation is defined
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order Morphisms.
From DomainTheory.Lang Require Import
     PCF_Syntax 
     PCF_Operational 
     PCF_Denotational 
     PCF_Soundness 
     PCF_Adequacy.


(* ================================================================== *)
(*  §1  Base expressions                                              *)
(* ================================================================== *)
(*
    The simplest PCF programs are closed expressions built from
    literals, arithmetic, comparison, and branching.  Each evaluates
    to a closed value via the big-step relation [e =>  v].
*)

(* A literal value evaluates to itself. *)
Example eval_lit : VAL (NLIT 42) ⇓ NLIT 42.
Proof. apply e_Val. Qed.

(* Arithmetic: 3 + 4 = 7. *)
Example eval_add : OP Nat.add (NLIT 3) (NLIT 4) ⇓ NLIT 7.
Proof. apply e_Op. Qed.

(* Comparison: 5 > 3 is true  (GT computes n2 <? n1). *)
Example eval_gt : GT (NLIT 5) (NLIT 3) ⇓ BLIT true.
Proof. apply e_Gt. Qed.

(* If-then-else: if true then 1 else 0  evaluates to 1. *)
Example eval_if :
    IFB (BLIT true) (VAL (NLIT 1)) (VAL (NLIT 0)) ⇓ NLIT 1.
Proof. apply e_IfTrue. apply e_Val. Qed.

(* Projection: fst (1, true) = 1. *)
Example eval_fst :
    FST (PAIR (NLIT 1) (BLIT true)) ⇓ NLIT 1.
Proof. apply e_Fst. Qed.


(* ================================================================== *)
(*  §2  Function application                                          *)
(* ================================================================== *)
(*
    Functions in PCF are introduced by [FIX tau1 tau2 body], which
    binds TWO variables in [body]:
    - index 0 (ZVAR)      = the argument   (type tau1)
    - index 1 (SVAR ZVAR) = the function itself (type tau1 →ₜ tau2)

    Application [APP f v] triggers double substitution of the argument
    and the function into the body, then evaluates the result.
*)

(* The identity function on Nat. *)
Definition pcf_id : CValue (Nat →ₜ Nat) :=
  FIX Nat Nat (VAL (VAR ZVAR)).

(* id 5 = 5. *)
Example eval_id : APP pcf_id (NLIT 5) ⇓ NLIT 5.
Proof. apply e_App. apply e_Val. Qed.

(* The constant-42 function. *)
Definition pcf_const42 : CValue (Nat →ₜ Nat) :=
  FIX Nat Nat (VAL (NLIT 42)).

(* const42 0 = 42. *)
Example eval_const42 : APP pcf_const42 (NLIT 0) ⇓ NLIT 42.
Proof. apply e_App. apply e_Val. Qed.

(* The doubling function:  double(x) = x + x. *)
Definition pcf_double : CValue (Nat →ₜ Nat) :=
  FIX Nat Nat (OP Nat.add (VAR ZVAR) (VAR ZVAR)).

(* double 7 = 14. *)
Example eval_double : APP pcf_double (NLIT 7) ⇓ NLIT 14.
Proof. apply e_App. apply e_Op. Qed.

(* The factorial function *)
Definition factorial : CValue (Nat →ₜ Nat) :=
  FIX Nat Nat 
    (LET (GT (VAR ZVAR) (NLIT 0))
        (IFB (VAR ZVAR)
            (LET (OP Nat.sub (VAR (SVAR ZVAR)) (NLIT 1)) 
                 (LET (APP (VAR (SVAR (SVAR (SVAR ZVAR)))) (VAR ZVAR))
                    (OP Nat.mul (VAR ZVAR) (VAR (SVAR (SVAR (SVAR ZVAR)))))
                 )
            )
            
            (VAL (NLIT 1))
        )).

(* Automation for PCF evaluation proofs: try each big-step rule. *)
Local Ltac pcf_eval :=
  simpl;
  first
    [ apply e_Val
    | apply e_Op
    | apply e_Gt
    | apply e_Fst
    | apply e_Snd
    | apply e_IfTrue; pcf_eval
    | apply e_IfFalse; pcf_eval
    | eapply e_Let; [pcf_eval | pcf_eval]
    | apply e_App; pcf_eval ].

Example eval_factorial_5 : APP factorial (NLIT 5) ⇓ NLIT 120.
Proof. pcf_eval. Qed.


(* ================================================================== *)
(*  §3  Denotational semantics                                        *)
(* ================================================================== *)
(*
    Every closed expression [e : CExp tau] has a denotation
    [sem_cexp e : option (sem_ty tau)].  The outer [option] models
    partiality:  [None] means divergence, [Some d] means convergence
    to the semantic value [d].

    For closed values, [sem_cval v : sem_ty tau] gives the semantic
    value directly (values always converge).
*)

(* Denotation of a literal. *)
Example den_lit : ⟦ VAL (NLIT 42) ⟧ᶜₑ = Some 42.
Proof. reflexivity. Qed.

(* Denotation of addition. *)
Example den_add : ⟦ OP Nat.add (NLIT 3) (NLIT 4) ⟧ᶜₑ = Some 7.
Proof. reflexivity. Qed.

(* Denotation of comparison. *)
Example den_gt : ⟦ GT (NLIT 5) (NLIT 3) ⟧ᶜₑ = Some true.
Proof. reflexivity. Qed.

(* Denotation of if-then-else. *)
Example den_if :
    ⟦ IFB (BLIT true) (VAL (NLIT 1)) (VAL (NLIT 0)) ⟧ᶜₑ = Some 1.
Proof. reflexivity. Qed.

(*  For programs that use [FIX], the denotational semantics involves
    the least fixed-point operator [fixp], which does not reduce by
    computation.  Instead, we obtain denotational results from
    operational proofs via soundness (see §4 below).  *)


(* ================================================================== *)
(*  §4  Soundness                                                     *)
(* ================================================================== *)
(*
    The soundness theorem relates operational evaluation to denotation:

        e =>  v   implies   sem_exp e tt = Some (sem_val v tt)

    In other words: if a program evaluates to a value, then its
    denotation equals [Some] of the value's denotation.  This is the
    "easy" direction of the correspondence.
*)

(* Soundness applied to id 5. *)
Example sound_id :
    ⟦ APP pcf_id (NLIT 5) ⟧ᶜₑ = Some ⟦ NLIT 5 ⟧ᶜᵥ.
Proof. exact (soundness _ _ eval_id). Qed.

(* Soundness applied to double 7. *)
Example sound_double :
    ⟦ APP pcf_double (NLIT 7) ⟧ᶜₑ = Some ⟦ NLIT 14 ⟧ᶜᵥ.
Proof. exact (soundness _ _ eval_double). Qed.


(* ================================================================== *)
(*  §5  Adequacy                                                      *)
(* ================================================================== *)
(*
    The adequacy theorem gives the "hard" direction:

        sem_exp e tt <> None   implies   e ⇓

    Combined with soundness, this yields:

        e ⇓   iff   sem_exp e tt <> None

    (the full correspondence [convergence_iff_defined]).

    In words: a closed expression converges operationally if and only
    if its denotation is not bottom (None).
*)

(* The denotation of 3+4 is defined (computes to [Some 7]). *)
Example defined_add : ⟦ OP Nat.add (NLIT 3) (NLIT 4) ⟧ᶜₑ <> None.
Proof. discriminate. Qed.

(* By adequacy, 3+4 converges -- deduced purely from the denotation. *)
Example converges_add : OP Nat.add (NLIT 3) (NLIT 4) ⇓.
Proof. exact (adequacy _ defined_add). Qed.

(* For FIX-based programs whose denotation involves [fixp], we
   derive convergence from the operational evaluation instead. *)
Example converges_id : APP pcf_id (NLIT 5) ⇓.
Proof. exact (eval_converges _ _ eval_id). Qed.

(* The full correspondence for double 7. *)
Example iff_double :
    APP pcf_double (NLIT 7) ⇓  <->
    ⟦ APP pcf_double (NLIT 7) ⟧ᶜₑ <> None.
Proof. exact (convergence_iff_defined _). Qed.
