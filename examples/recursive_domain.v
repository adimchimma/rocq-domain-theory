(*  recursive_domain -- Solving a recursive domain equation.

    This file demonstrates the bilimit machinery for constructing
    recursive domains.  A *mixed-variance locally-continuous functor*
    F(X^{op}, X) on a CPO-enriched category admits a canonical
    solution  D_inf  to the equation  D ~= F(D, D)  -- the inverse
    limit of a sequence of approximations.

    The concrete functor shipped with the library is the *lifted
    function-space* bifunctor  FL(A, B) = [A ->c B]_bot  registered
    on CPO.type by [instances/FunLift.v].  It solves:

        D_inf  ~=  [D_inf ->c D_inf]_bot

    Contents:
    - S1  Abstract bilimit -- ROLL/UNROLL isomorphism in any
          MixedLCFunctor
    - S2  Concrete functor -- CPO.type with FL_obj
    - S3  Approximation tower -- the sequence D0, F(D0,D0), ...
    - S4  Properties -- deflation chain, sup = id
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms Enriched.
From DomainTheory.Theory Require Import
  DomainEquations FunctionSpaces Lift OrderTheory CPOTheory EnrichedTheory.
From DomainTheory.Instances Require Import Discrete Function FunLift.


(* ================================================================== *)
(*  S1  Abstract bilimit: ROLL / UNROLL isomorphism                   *)
(* ================================================================== *)
(*
    Given any [MixedLCFunctor] F on a CPO-enriched category C, a
    starting object D0, and an initial EP-pair  D0 <-> F(D0,D0),
    the bilimit axiom furnishes:

    - [D_inf]   : the recursive domain  (D_inf ~= F(D_inf, D_inf))
    - [ROLL]    : F(D_inf, D_inf) ->  D_inf
    - [UNROLL]  : D_inf -> F(D_inf, D_inf)
    - [ROLL o UNROLL = id]  and  [UNROLL o ROLL = id]

    All definitions live in [DomainEquations.v S7].
*)

Section AbstractBilimit.
Context {C : MixedLCFunctor.type} (D0 : C)
        (ep0 : ep_pair D0 (MF_obj D0 D0)).

(* The isomorphism laws follow directly from the bilimit record. *)
Example roll_unroll : ROLL D0 ep0 ⊚ UNROLL D0 ep0 = id_mor (D_inf D0 ep0).
Proof. exact (bil_iso_roll_unroll D0 ep0). Qed.

Example unroll_roll :
    UNROLL D0 ep0 ⊚ ROLL D0 ep0 = id_mor (MF_obj (D_inf D0 ep0) (D_inf D0 ep0)).
Proof. exact (bil_iso_unroll_roll D0 ep0). Qed.

(* The isomorphism packaged as an EP-pair in both directions. *)
Example iso_ep : ep_pair (D_inf D0 ep0) (MF_obj (D_inf D0 ep0) (D_inf D0 ep0)).
Proof. exact (bil_lim_iso D0 ep0). Qed.

Example iso_ep_inv : ep_pair (MF_obj (D_inf D0 ep0) (D_inf D0 ep0)) (D_inf D0 ep0).
Proof. exact (bil_lim_iso_inv D0 ep0). Qed.

End AbstractBilimit.


(* ================================================================== *)
(*  S2  Concrete functor: lifted function-space on CPO.type           *)
(* ================================================================== *)
(*
    The file [instances/FunLift.v] registers CPO.type as a
    MixedLCFunctor with:

        MF_obj A B  =  FL_obj A B  =  [A ->c B]_bot

    So the solved equation is   D_inf ~= [D_inf ->c D_inf]_bot.

    To instantiate the bilimit we need a starting object and an
    initial EP-pair.  The unit CPO is the simplest choice:
    the projection is the constant-tt map, the embedding sends
    tt to bottom (None).
*)

Section ConcreteSetup.

Let D0 : CPO.type := unit.

(* Build the initial EP-pair   unit <-> [unit ->c unit]_bot. *)

(* Embedding: tt |-> None (bottom of the lifted function space). *)
Definition unit_emb : [unit →c ⟨[unit →c unit]⟩⊥] := cont_const None.

(* Projection: everything |-> tt (the only element of unit). *)
Definition unit_proj : [⟨[unit →c unit]⟩⊥ →c unit] := cont_const tt.

Lemma unit_ep_retract :
    cont_comp unit_proj unit_emb = @cont_id unit.
Proof.
  apply cont_fun_ext. intros []; reflexivity.
Qed.

Lemma unit_ep_deflation :
    cont_comp unit_emb unit_proj ⊑ @cont_id ⟨[unit →c unit]⟩⊥.
Proof.
  intros x. simpl. exact I.
Qed.

End ConcreteSetup.


(* ================================================================== *)
(*  S3  Approximation tower                                           *)
(* ================================================================== *)
(*
    The bilimit machinery builds the approximation sequence:

        D_0 = D0,   D_{n+1} = F(D_n, D_n)

    with EP-pairs  D_n <-> D_{n+1}  at each stage, and assembles
    the colimit [D_inf] together with cone morphisms.

    [mf_approx_obj D0 n]  gives the n-th approximation.
    [bil_cone_ep D0 ep0 n] gives the EP-pair  D_n <-> D_inf.
*)

Section Tower.
Context {C : MixedLCFunctor.type} (D0 : C)
        (ep0 : ep_pair D0 (MF_obj D0 D0)).

(* First few levels of the tower. *)
Example tower_0 : mf_approx_obj D0 0 = D0.
Proof. reflexivity. Qed.

Example tower_1 : mf_approx_obj D0 1 = MF_obj D0 D0.
Proof. reflexivity. Qed.

Example tower_2 :
    mf_approx_obj D0 2 = MF_obj (MF_obj D0 D0) (MF_obj D0 D0).
Proof. reflexivity. Qed.

(* Each approximation embeds into D_inf. *)
Example cone_ep_0 : ep_pair (mf_approx_obj D0 0) (D_inf D0 ep0).
Proof. exact (bil_cone_ep D0 ep0 0). Qed.

End Tower.


(* ================================================================== *)
(*  S4  Deflation chain and completeness                              *)
(* ================================================================== *)
(*
    The cone projections compose with embeddings to form a chain of
    *deflations* (idempotents below the identity):

        delta_n  =  emb_n o proj_n  :  D_inf -> D_inf

    This chain is increasing, and its supremum is the identity:

        sup_n delta_n  =  id

    This property characterises D_inf as the *colimit* of the tower.
*)

Section Deflations.
Context {C : MixedLCFunctor.type} (D0 : C)
        (ep0 : ep_pair D0 (MF_obj D0 D0)).

(* Each deflation is below the identity. *)
Example defl_below_id (n : nat) :
    (bil_defl_chain D0 ep0).[n] ⊑ id_mor (D_inf D0 ep0).
Proof. exact (bil_cone_deflation (bilimit_exists D0 ep0) n). Qed.

(* The supremum of all deflations is the identity -- completeness. *)
Example sup_defls_eq_id :
    ⊔ (bil_defl_chain D0 ep0) = id_mor (D_inf D0 ep0).
Proof. exact (bil_sup_deflations D0 ep0). Qed.

End Deflations.
