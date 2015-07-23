Require Export System.

Inductive HumanUsable (sys_type: SystemType) : Prop :=
  satisfiesHumanUsabilityRequirements:
    (exists humanUsable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, humanUsable c p s st) ->
        HumanUsable sys_type.