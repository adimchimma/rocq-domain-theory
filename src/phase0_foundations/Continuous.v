(** Continuous functions

    Definitions and lemmas for continuity and continuous functions.
*)

From phase0_foundations Require Import CPO Order.
Import Order.

Module Continuous.

(** A function is continuous if it preserves lubs of ω-chains. 
    Continuity assumes the function is already monotone. *)
Definition continuous (D E : Cpo.cpo) (f : mono_fun (Cpo.cpo_pre D) (Cpo.cpo_pre E)) : Prop :=
  forall (c : chain (Cpo.cpo_pre D)),
    f (Cpo.lub_of_chain D c) = Cpo.lub_of_chain E (map_chain (Cpo.cpo_pre D) (Cpo.cpo_pre E) f c).

Record cont_fun (D E : Cpo.cpo) := {
  cf_mfun :> mono_fun (Cpo.cpo_pre D) (Cpo.cpo_pre E) ;
  cf_cont : continuous D E cf_mfun
}.

(* No global coercion declared to avoid name collisions; use `cf_mfun` explicitly *)

Lemma id_continuous (D : Cpo.cpo) : 
  continuous D D (Build_mono_fun (Cpo.cpo_pre D) (Cpo.cpo_pre D) (fun x => x) (fun _ _ H => H)).
Proof. 
  intros c. 
  (* TODO: Prove that map_chain with identity is the same chain *)
  admit.
Admitted.

End Continuous.
