
Inductive Ross_Adaptable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesRoss_AdaptabilityRequirement: 
    (exists ross_adaptable: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_adaptable sys sh cx ps)) ->
    Ross_Adaptable System Stakeholder Context Phase sys.