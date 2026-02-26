(** * Lift

    Phase 0: Lifting construction (flat domain with added bottom).

    Definitions to be added:
    - [lift A]: the type [option A] with a flat order
      ([None] is bottom; [Some x] and [Some y] are related iff [x = y]).
    - CPO structure on [lift A].
    - [ret : A -> lift A] as the unit of the lifting monad.
    - Continuity of [ret] and of [bind].
*)
