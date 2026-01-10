(** Lift monad

    Minimal notes and API placeholder for the lift/option monad on CPOs.
    Full implementation will follow once Pointed/Lub helpers are finalized.
*)

Module Lift.
  (** Intended API:
      - Given a pointed cpo D, `lift D` is a cpo with an added bottom element
        representing divergence.
      - Provide `ret` and `bind` operations, and proofs of monotonicity.

      Implementation: TODO (planned after Pointed and Sums are stabilized).
  *)
End Lift.
