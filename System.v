(** * System Model *)

Record System := mk_sys {
  Contexts: Set;
  Stakeholders: Set;
  Phases: Set;
  Artifacts: Set;
  Value: Set;
  artifacts: Artifacts;
  value: Value
}.