Inductive Manufacturable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (manufacturable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesManufacturabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, manufacturable sys sh cx ps) ->
      Manufacturable System Stakeholder Context Phase sys manufacturable.