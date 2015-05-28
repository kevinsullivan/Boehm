
Inductive Ross_Survivable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (ross_survivable: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesRoss_SurvivabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_survivable sys sh cx ps) ->
      Ross_Survivable System Stakeholder Context Phase sys ross_survivable.