
Inductive FunctionalVersatile (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesFunctionalVersatilityRequirement: 
    (exists functionalVersatile: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, functionalVersatile sys sh cx ps)) ->
    FunctionalVersatile System Stakeholder Context Phase sys.