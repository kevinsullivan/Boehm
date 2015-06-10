(** Maintainable General Theory *)
Require Export System.

Inductive Maintainable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesMaintainabilityRequirement:
    (exists maintainable: System msys -> Prop, maintainable sys) -> Maintainable sys.