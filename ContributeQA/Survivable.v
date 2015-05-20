Inductive Survivable (System: Set) (Context: Set) (sys: System) 
                     (survivable: System -> Context -> Prop) : Prop :=
  satisfiesSurvivabilityRequirement:
    (forall cx: Context, survivable sys cx) ->
      Survivable System Context sys survivable.
