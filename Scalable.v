Require Export System.

Inductive Scalable (sys_type: SystemType) : Prop :=
  satisfiesScalabilityRequirements:
    (exists scalable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, scalable c p s st) ->
        Scalable sys_type.