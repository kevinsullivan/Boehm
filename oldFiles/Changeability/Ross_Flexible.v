
Inductive Ross_Flexible (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesRoss_FlexibilityRequirement: 
  (exists ross_flexible: System -> Stakeholder -> Context  -> Phase -> Prop,
      (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_flexible sys sh cx ps)) ->
  Ross_Flexible System Stakeholder Context Phase sys.