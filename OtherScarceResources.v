Require Export System.

Inductive OtherScarceResources (sys_type: SystemType) : Prop :=
  satisfiesOtherResourcesRequirements:
    (exists otherScarceResources: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, otherScarceResources c p s st) ->
        OtherScarceResources sys_type.