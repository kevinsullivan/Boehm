
Inductive OperationalReconfigurable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (operationalReconfigurable: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesAdaptabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, operationalReconfigurable sys sh cx ps) ->
      OperationalReconfigurable System Stakeholder Context Phase sys operationalReconfigurable.