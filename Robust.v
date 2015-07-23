Require Export System.

Inductive Robust (sys_type: SystemType) : Prop :=
  satisfiesRobustnessRequirements:
    (exists robust: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, robust c p s st) ->
        Robust sys_type.