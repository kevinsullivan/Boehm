Inductive Versatile (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (versatile: System -> Stakeholder -> Context -> Prop) : Prop :=
  satisfiesVersatilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, versatile sys sh cx) ->
      Versatile System Stakeholder Context sys versatile.
