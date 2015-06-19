(** * STATE MODULE *)
(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)
(** 
This module defines the [State], which represents a system's state, 
including internal state and external state, that are success-critical
for the stakeholders of the system. "State" is a component of the "Context."
*)

Module State.
  Inductive InternalState := anInternalState.
  Inductive ExternalState := anExternalState.
  Inductive State := mk_state: InternalState -> ExternalState -> State.
End State.
