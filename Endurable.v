Require Export System.

Inductive Endurable (sys_type: SystemType) : Prop :=
  satisfiesEndurabilityRequirements:
    (exists endurable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, endurable c p s st) ->
        Endurable sys_type.