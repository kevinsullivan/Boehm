
Inductive FormReconfigurable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (formReconfigurable: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesFormReconfigurabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, formReconfigurable sys sh cx ps) ->
      FormReconfigurable System Stakeholder Context Phase sys formReconfigurable.