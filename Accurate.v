Require Export System.

Inductive Accurate (sys_type: SystemType): Prop :=
  satisfiesAccuracyRequirements:
    (exists accurate: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, accurate c p s st) ->
        Accurate sys_type.