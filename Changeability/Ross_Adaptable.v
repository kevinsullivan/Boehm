
Inductive Ross_Adaptable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (ross_adaptable: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesRoss_AdaptabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_adaptable sys sh cx ps) ->
      Ross_Adaptable System Stakeholder Context Phase sys ross_adaptable.