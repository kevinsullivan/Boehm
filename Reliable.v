(** Reliability General Theory *)
Require Export System.

Inductive Reliable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesReliabilityRequirement:
    (exists reliable: System msys -> Prop, reliable sys) -> Reliable sys.

