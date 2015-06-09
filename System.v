(** * System Model *)

(**
We factor system models into separate modules. This file provides
a template for system models, capturing common elements of all such
models, as needed by our overall framework.
*)

(** An instance of SystemType is a collection of 5 sets, where each
    is a representation of a different aspect of a System in our model *)
Record SystemType := mk_system_type { 
  stakeholders: Set;
  resources: Set;
  phases: Set;
  contexts: Set;
  SystemModel: Set
}.

(** Begin the running example: A SystemType whose stakeholders, resources, phases,
    and contexts are all simply unit, and whose SystemModel is bool *)
Definition UnitBoolType: SystemType := mk_system_type unit unit unit unit bool.

(** In order to actually build a System, we need to supply an
    instance of the SystemType's SystemModel. This will be a bool in our example.
    This constructor basically fetches the Type information from the SystemType record
    and requires an instance of whatever the SystemModel is for that SystemType to construct
    an instance of [System sysType] *)
Inductive System (a: SystemType): Type :=
  mk_system: (SystemModel a) -> System a.

(** And here's our System  *)
Definition UnitBoolSystem := System UnitBoolType.

(** It lives in [Set] *)
Check UnitBoolSystem.

(** Dependent types are amazing! This function is a "getter" parameterized
    by like 7 types, and its return type depends on those types as well!
    We'll use this to reason about the state of our system in our example
    to determine if we want to deem it Changeable. *)
Definition getState {a: SystemType} (s: System a) : (SystemModel a) :=
  match s with
      mk_system state => state
  end.

(** This is how the "capital-letter"-ility relations will look now for
    all of our ilities. It requires only a System (and a SystemType,
    but this can be inferred from the instance given).
    Basically, we're saying
    "If you can give me a callback that takes a [System sysType] and
     shows that its changeable, I'll agree that it's changeable.
    This simply serves as a generic interface to plug in to. *)
Inductive Changeable {sysType: SystemType} (sys: System sysType) : Prop :=
  satisfiesChangeabilityRequirement:
    (exists changeable: System sysType -> Prop, changeable sys) ->
    Changeable sys.

(** Model-specific logic here, this is our callback!
    We'll make use of our system model and specify
    that only "true" systems are changeable. *)

(** An example property for our system model. *)
Inductive true_system: UnitBoolSystem -> Prop :=
  is_true: forall sys: UnitBoolSystem, (getState sys = true) -> true_system sys.

Inductive unit_bool_changeable: UnitBoolSystem -> Prop :=
  truth_is_changeable: forall sys: UnitBoolSystem, true_system sys -> unit_bool_changeable sys.

Example system_instance: UnitBoolSystem := mk_system UnitBoolType true.

Theorem instance_is_changeable: Changeable system_instance.
Proof.
  (** Generic framework *)
  constructor.
  (** Little-c changeable *)
  exists unit_bool_changeable.
  intros.
  (** Domain and model-specific reasoning *)
  apply truth_is_changeable.
  apply is_true.
  simpl. reflexivity.
Qed.

(** TODO: Adapt this to the car example *)
