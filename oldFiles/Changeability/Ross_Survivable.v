
Inductive Ross_Survivable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesRoss_SurvivabilityRequirement: 
    (exists ross_survivable: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_survivable sys sh cx ps)) ->
    Ross_Survivable System Stakeholder Context Phase sys.