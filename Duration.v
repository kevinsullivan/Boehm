(** Duration General Theory *)
Require Export System.

Inductive Duration {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesDurationRequirement:
    (exists duration: System msys -> Prop, duration sys) -> Duration sys.