(** Maneuverable General Theory *)
Require Export System.

Inductive Maneuverable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesManeuverabilityRequirement:
    (exists maneuverable: System msys -> Prop, maneuverable sys) -> Maneuverable sys.