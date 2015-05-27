Inductive Sustainable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (sustainable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesSustainabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, sustainable sys sh cx ps) ->
      Sustainable System Stakeholder Context Phase sys sustainable.