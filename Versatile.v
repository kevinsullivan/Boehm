(** Versatility General Theory *)
Require Export System.

Inductive Versatile {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesVersatilityRequirement:
    (exists versatile: System msys -> Prop, versatile sys) -> Versatile sys.
