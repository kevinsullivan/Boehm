
Inductive ValueSurvivable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesValueSurvivabilityRequirement: 
    (exists valueSurvivable: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, valueSurvivable sys sh cx ps)) ->
    ValueSurvivable System Stakeholder Context Phase sys.