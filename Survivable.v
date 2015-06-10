(** Survivability General Theory *)
Require Export System.

Inductive Survivable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesSurvivabilityRequirement:
    (exists survivable: System msys -> Prop, survivable sys) -> Survivable sys.