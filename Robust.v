(** Robustness General Theory *)
Require Export System.

Inductive Robust {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesRobustnessRequirement:
    (exists robust: System msys -> Prop, robust sys) -> Robust sys.
