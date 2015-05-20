Inductive Reliable (System: Set) (Context: Set) (sys: System) 
                     (reliable: System -> Context -> Prop) : Prop :=
  satisfiesReliabilityRequirement:
    (forall cx: Context, reliable sys cx) ->
      Reliable System Context sys reliable.
