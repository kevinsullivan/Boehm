Inductive Versatile (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (versatile: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesVersatilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, versatile sys sh cx ps) ->
      Versatile System Stakeholder Context Phase sys versatile.
