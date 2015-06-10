(** Speed General Theory *)
Require Export System.

Inductive Speed {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesSpeedRequirement:
    (exists speed: System msys -> Prop, speed sys) -> Speed sys.
