Inductive Survivable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (survivable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesSurvivabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, survivable sys sh cx ps) ->
      Survivable System Stakeholder Context Phase sys survivable.