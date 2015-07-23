Require Export System.

Inductive Versatile (sys_type: SystemType) : Prop :=
  satisfiesVersatilityRequirements:
    (exists versatile: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, versatile c p s st) ->
        Versatile sys_type.
