
Inductive Exchangeable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (exchangeable: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesExchangeabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, exchangeable sys sh cx ps) ->
      Exchangeable System Stakeholder Context Phase sys exchangeable.