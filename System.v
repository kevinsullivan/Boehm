(** * System Model *)

(** The [Environment] is the set of conditions surrounding the system. *)
Record Environment := mk_environment {
  stakeholders: Set;
  resources: Set;
  phases: Set;
  contexts: Set
}.

(** A Model is an Environment and a state model *)
Record Model := mk_model {
  environment: Environment;
  state: Set
}.

(** Begin the running example: A SystemType whose stakeholders, resources, phases,
    and contexts are all simply unit, and whose State model is bool *)
Definition unit_environment: Environment := mk_environment unit unit unit unit.

Definition unit_bool_model: Model := mk_model unit_environment bool.

(** In order to actually build a System, we need to supply an
    instance of the SystemType's SystemModel. This will be a bool in our example.
    This constructor basically fetches the Type information from the SystemType record
    and requires an instance of whatever the SystemModel is for that SystemType to construct
    an instance of [System sysType] *)
Inductive System (a: Model): Type :=
  mk_system: (state a) -> System a.

(** And here's our System  *)
Definition UnitBoolSystem := System unit_bool_model. 

(** It lives in [Set] *)
Check UnitBoolSystem.

(** Dependent types are amazing! This function is a "getter" parameterized
    by like 7 types, and its return type depends on those types as well!
    We'll use this to reason about the state of our system in our example
    to determine if we want to deem it Changeable. *)
Definition getState {a: Model} (s: System a) : (state a) :=
  match s with
      mk_system st => st
  end.

(** This is how the "capital-letter"-ility relations will look now for
    all of our ilities. It requires only a System (and a SystemType,
    but this can be inferred from the instance given).
    Basically, we're saying
    "If you can give me a callback that takes a [System sysType] and
     shows that its changeable, I'll agree that it's changeable."
    This simply serves as a generic interface to plug in to. *)

Inductive Changeable {model: Model} (sys: System model) : Prop :=
  satisfiesChangeabilityRequirement:
    (exists changeable: System model -> Prop, changeable sys) ->
    Changeable sys.

(** Model-specific logic here, this is our callback!
    We'll make use of our system model and specify
    that only "true" systems are changeable. *)

(** An example property for our system model. *)
Inductive true_system: UnitBoolSystem -> Prop :=
  is_true: forall sys: UnitBoolSystem, (getState sys = true) -> true_system sys.

Inductive unit_bool_changeable: UnitBoolSystem -> Prop :=
  truth_is_changeable: forall sys: UnitBoolSystem, true_system sys -> unit_bool_changeable sys.

Example system_instance: UnitBoolSystem := mk_system unit_bool_model true.

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
