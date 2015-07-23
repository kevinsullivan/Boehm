Require Export System.

Inductive Duration (sys_type: SystemType) : Prop :=
  satisfiesDurationRequirements:
    (exists duration: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, duration c p s st) ->
        Duration sys_type.