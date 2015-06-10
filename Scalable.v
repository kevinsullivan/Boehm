(** Scalable General Theory *)
Require Export System.

Inductive Scalable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesScalabilityRequirement:
    (exists scalable: System msys -> Prop, scalable sys) -> Scalable sys.