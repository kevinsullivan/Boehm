(** Physical Capable General Theory *)
Require Export System.

Inductive PhysicalCapable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesPhysicalCapabilityRequirement:
    (exists physicalCapable: System msys -> Prop, physicalCapable sys) -> PhysicalCapable sys.
