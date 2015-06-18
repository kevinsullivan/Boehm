(** * System Model *)

Record SystemType := mk_system_type {
  Contexts: Set;
  Stakeholders: Set;
  Phases: Set;
  ArtifactType: Set;
  ValueType: Set
}.

(**
A system instance models a system of a particular type in a particular state.
The state includes the current context and phase, the current state of the 
artifact itself, and the current accounting/value state of the artifact.
Note that an individual stakeholder is not part of the system state, but
rather someone or something that could effect a change or be affected by 
one.
*)

Inductive SystemInstance {sys_type: SystemType}: Type := mk_system {
    context: (Contexts sys_type)
  ; phase: (Phases sys_type)
  ; artifact: (ArtifactType sys_type)
  ; value: (ValueType sys_type) 
}.

