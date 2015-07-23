Require Export System.

Inductive Speed (sys_type: SystemType) : Prop :=
  satisfiesSpeedRequirements:
    (exists speed: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, speed c p s st) ->
        Speed sys_type.