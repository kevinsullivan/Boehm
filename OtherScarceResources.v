(** *)
Require Export System.

Inductive OtherScarceResources {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesOtherResourcesRequirement:
    (exists otherResources: System msys -> Prop, otherResources sys) -> OtherScarceResources sys.