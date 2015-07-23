Require Export System.

Inductive Maintainable (sys_type: SystemType) : Prop :=
  satisfiesMaintainabilityRequirements:
    (exists maintainable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, maintainable c p s st) ->
        Maintainable sys_type.