
Inductive FunctionalVersatile (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (functionalVersatile: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesFunctionalVersatilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, functionalVersatile sys sh cx ps) ->
      FunctionalVersatile System Stakeholder Context Phase sys functionalVersatile.