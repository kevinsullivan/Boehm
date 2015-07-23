Require Export System.

Inductive Manufacturable (sys_type: SystemType) : Prop :=
  satisfiesManufacturabilityRequirements:
    (exists manufacturable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, manufacturable c p s st) ->
        Manufacturable sys_type.