
Inductive OperationalVersatile (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (operationalVersatile: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesOperationalVersatilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, operationalVersatile sys sh cx ps) ->
      OperationalVersatile System Stakeholder Context Phase sys operationalVersatile.