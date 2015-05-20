Inductive Manufacturable (System: Set) (Context: Set) (sys: System) 
                              (manufacturable: System -> Context -> Prop) : Prop :=
  satisfiesManufacturabilityRequirement:
    (forall cx: Context, manufacturable sys cx) ->
      Manufacturable System Context sys manufacturable.
