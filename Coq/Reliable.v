Require Export System.

Inductive Reliable (sys_type: SystemType) : Prop :=
  satisfiesReliabilityRequirements:
    (exists reliable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, reliable c p s st) ->
        Reliable sys_type.