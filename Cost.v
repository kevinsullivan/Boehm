(** Cost General Theory *)
Require Export System.

Inductive Cost {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesCostRequirement:
    (exists cost: System msys -> Prop, cost sys) -> Cost sys.
