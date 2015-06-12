(** * System Model *)

Record MetaSystem := mk_msys {
  Stakeholders: Set;
  Resources: Set;
  Phases: Set;
  Contexts: Set;
  Artifacts: Set;
  stakeholders: Stakeholders;
  resources: Resources;
  phases: Phases;
  contexts: Contexts;
  artifacts: Artifacts
}.

(** Begin the running example: A model whose stakeholders, resources, phases,
    and contexts are all simply unit, and whose state type is bool *)

Definition unit_bool_model: MetaSystem := mk_msys unit unit unit unit bool.

Inductive System (msys: MetaSystem): Type :=
  mk_system: (system_type msys) -> System msys.

Definition UnitBoolSystem := System unit_bool_model. 

Check UnitBoolSystem.

(** Dependent types are amazing! This function is a "getter" parameterized
    by like 7 types, and its return type depends on those types as well!
    We'll use this to reason about the state of our system in our example
    to determine if we want to deem it Changeable. *)

Definition getState {msys: MetaSystem} (sys: System msys) : (system_type msys) :=
  match sys with
      mk_system st => st
  end.

(** This is how the "capital-letter"-ility relations will look now for
    all of our ilities. It requires only a System (and a Model,
    but this can be inferred from the instance given).
    Basically, we're saying
    "If you can give me a callback that takes a [System model] and
    shows that its changeable, I'll agree that it's changeable."
    This simply serves as a generic interface to plug in to. *)

Inductive Changeable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesChangeabilityRequirement:
    (exists changeable: System msys -> Prop, changeable sys) ->
    Changeable sys.

(** Model-specific logic here, this is our callback!
    We'll make use of our system model and specify
    that only "true" systems are changeable. *)

(** An example property for our system model. *)
Inductive true_system: UnitBoolSystem -> Prop :=
  is_true: forall sys: UnitBoolSystem, (getState sys = true) -> true_system sys.

Inductive unit_bool_changeable: UnitBoolSystem -> Prop :=
  truth_is_changeable:
    forall sys: UnitBoolSystem, true_system sys -> unit_bool_changeable sys.

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