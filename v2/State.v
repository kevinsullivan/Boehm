(** * STATE MODULE *)
(** This module defines the state that a context is.*)

Module State.
  Inductive InternalState := anInternalState.
  Inductive ExternalState := anExternalState.
  Inductive State := mk_state: InternalState -> ExternalState -> State.
End State.                                                                                                                                                                              