(** Impact General Theory *)
Require Export System.

Inductive Impactful {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesImpactRequirement:
    (exists impactful: System msys -> Prop, impactful sys) -> Impactful sys.
