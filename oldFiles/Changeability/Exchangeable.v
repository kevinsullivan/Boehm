
Inductive Exchangeable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesExchangeabilityRequirement: 
    (exists exchangeable: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, exchangeable sys sh cx ps)) ->
    Exchangeable System Stakeholder Context Phase sys.