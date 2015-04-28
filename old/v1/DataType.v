(** * Draft Coq Spec derived from Boehm 2015 QA Ontology *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

(** ** SYSTEM **)

(** 
We can't concretely specify non-functional properties absent a model of the system.
We introduce a data type of system models, currently "stubbed out" as having only
one system model, [aSystem], without any further elaboration.
*)
Inductive System := aSystem.

(** ** CONTEXT *)

(**
Nor can we concretely specify system properties absent a model of its context. We
thus similarly introduce a data type of context models, expanded into multiple dimensions, 
including Referent, Stage and Stage. State can be expanded into two dimensions,
including InternalState and ExternalState, where both of them are currently "stubbed out" as having only
one concrete value, [anInternalStatea] and [anExternalState] respectively, without any further elaboration.
*)

Inductive Referent := aReferent.

Inductive InternalState := anInternalState.
Inductive ExternalState := anExternalState.
Inductive State := mk_state: InternalState -> ExternalState -> State.

Inductive Stage := aStage.

Inductive Context := mk_context: Referent -> State -> Stage -> Context.

(** ** STAKEHOLDERS **)

(** 
An important class of "subjective" properties concerns stakeholder satisfaction or value.
We thus introduce a data type of "stakeholders in a given system, [s]." The [Stakeholder]
data type is thus parameterized by a given system model of concern.
*)

Inductive Stakeholder (s: System) := aStakeholder.