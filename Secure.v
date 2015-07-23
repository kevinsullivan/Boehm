Require Export System.

Inductive Secure (sys_type: SystemType) : Prop :=
  satisfiesSecurityRequirements:
    (exists secure: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, secure c p s st) ->
        Secure sys_type.