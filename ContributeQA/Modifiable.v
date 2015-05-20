Inductive Modifiable (System: Set) (Context: Set) (sys: System) 
                     (modifiable: System -> Context -> Prop) : Prop :=
  satisfiesModifiabilityRequirement:
    (forall cx: Context, modifiable sys cx) ->
      Modifiable System Context sys modifiable.
