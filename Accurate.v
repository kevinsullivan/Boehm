(** Accuracy General Theory *)
Require Export System.

Inductive Accurate {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesAccuracyRequirement:
    (exists accurate: System msys -> Prop, accurate sys) -> Accurate sys.

Inductive Adaptable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesAdaptabilityRequirement:
    (exists adaptable: System msys -> Prop, adaptable sys) -> Adaptable sys.
