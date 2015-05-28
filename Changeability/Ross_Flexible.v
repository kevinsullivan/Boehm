
Inductive Ross_Flexible (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (ross_flexible: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesRoss_FlexibilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_flexible sys sh cx ps) ->
      Ross_Flexible System Stakeholder Context Phase sys ross_flexible.