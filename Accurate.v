(** Accuracy General Theory *)
Require Export System.

Inductive Accurate {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesAccuracyRequirement:
    (exists accurate: System msys -> Prop, accurate sys) -> Accurate sys.
