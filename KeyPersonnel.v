Require Export System.

Inductive KeyPersonnel (sys_type: SystemType) : Prop :=
  satisfiesKeyPersonnelRequirements:
    (exists keyPersonnel: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, keyPersonnel c p s st) ->
        KeyPersonnel sys_type.