(** HumanUsable General Theory *)
Require Export System.

Inductive HumanUsable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesHumanUsabilityRequirement:
    (exists humanUsable: System msys -> Prop, humanUsable sys) -> HumanUsable sys.

