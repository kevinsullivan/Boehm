(** * CONTEXT MODULE*)

Load Referent.
Load Stage.
Load State.
(**
Nor can we concretely specify system properties absent a model of its context. We
thus similarly introduce a data type of context models, expanded into multiple dimensions, 
including Referent, Stage and Stage. State can be expanded into two dimensions,
including InternalState and ExternalState, where both of them are currently "stubbed out" as having only
one concrete value, [anInternalStatea] and [anExternalState] respectively, without any further elaboration.
*)
Module Context.
  Inductive Context := mk_context: Referent.Referent -> State.State -> Stage.Stage -> Context.
End Context.
