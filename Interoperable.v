(** Interoperable General Theory *)
Require Export System.

Inductive Interoperable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesInteroperabilityRequirement:
    (exists interoperable: System msys -> Prop, interoperable sys) -> Interoperable sys.
