Require Export System.

Inductive Tailorable (sys_type: SystemType) : Prop :=
  satisfiesTailorabilityRequirements:
    (exists tailorable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, tailorable c p s st) ->
        Tailorable sys_type.