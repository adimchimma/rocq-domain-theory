(** Product constructions

    Thin wrapper around `CPO.prod_cpo` implemented in `CPO.v`.
*)

From phase0_foundations Require Import CPO Order.
Import Order.

Module Products.

  (** Product cpo: pointwise order and lubs *)
  Definition prod_cpo (A B : Cpo.cpo) : Cpo.cpo :=
    let pre : Order.preorder := Order.Build_preorder (carrier (Cpo.cpo_pre A) * carrier (Cpo.cpo_pre B)) (fun p q => (le (Cpo.cpo_pre A) (fst p) (fst q)) /\ (le (Cpo.cpo_pre B) (snd p) (snd q)))
      (fun p => conj (le_refl (Cpo.cpo_pre A) (fst p)) (le_refl (Cpo.cpo_pre B) (snd p)))
      (fun p q r Hpq Hqr => match Hpq with conj Hpq1 Hpq2 => match Hqr with conj Hqr1 Hqr2 => conj (le_trans (Cpo.cpo_pre A) _ _ _ Hpq1 Hqr1) (le_trans (Cpo.cpo_pre B) _ _ _ Hpq2 Hqr2) end end) in
    {| Cpo.cpo_pre := pre ;
       Cpo.lub_of_chain := fun (c : chain pre) =>
         (Cpo.lub_of_chain A (map_chain pre (Cpo.cpo_pre A) (Build_mono_fun pre (Cpo.cpo_pre A) fst (fun _ _ H => proj1 H)) c),
          Cpo.lub_of_chain B (map_chain pre (Cpo.cpo_pre B) (Build_mono_fun pre (Cpo.cpo_pre B) snd (fun _ _ H => proj2 H)) c)) ;
       Cpo.lub_upper := fun (c : chain pre) (n : nat) =>
         conj (Cpo.lub_upper A (map_chain pre (Cpo.cpo_pre A) (Build_mono_fun pre (Cpo.cpo_pre A) fst (fun _ _ H => proj1 H)) c) n)
              (Cpo.lub_upper B (map_chain pre (Cpo.cpo_pre B) (Build_mono_fun pre (Cpo.cpo_pre B) snd (fun _ _ H => proj2 H)) c) n) ;
       Cpo.lub_least := fun (c : chain pre) (p : carrier pre) (H : forall n, le pre (ch pre c n) p) =>
         let a := fst p in let b := snd p in
         conj (Cpo.lub_least A (map_chain pre (Cpo.cpo_pre A) (Build_mono_fun pre (Cpo.cpo_pre A) fst (fun _ _ H => proj1 H)) c) a (fun n => proj1 (H n)))
              (Cpo.lub_least B (map_chain pre (Cpo.cpo_pre B) (Build_mono_fun pre (Cpo.cpo_pre B) snd (fun _ _ H => proj2 H)) c) b (fun n => proj2 (H n)))
    |}.
End Products.
