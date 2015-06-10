(** Endurable General Theory *)
Require Export System.

Inductive Endurable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesEndurabilityRequirement:
    (exists endurable: System msys -> Prop, endurable sys) -> Endurable sys.
