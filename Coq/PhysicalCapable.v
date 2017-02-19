Require Export System.

Inductive PhysicalCapable (sys_type: SystemType) : Prop :=
  satisfiesPhysicalCapabilityRequirements:
    (exists physicalCapable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, physicalCapable c p s st) ->
        PhysicalCapable sys_type.