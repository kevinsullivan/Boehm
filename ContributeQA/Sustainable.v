Inductive Sustainable (System: Set) (Context: Set) (sys: System) 
                              (sustainable: System -> Context -> Prop) : Prop :=
  satisfiesSustainabilityRequirement:
    (forall cx: Context, sustainable sys cx) ->
      Sustainable System Context sys sustainable.
