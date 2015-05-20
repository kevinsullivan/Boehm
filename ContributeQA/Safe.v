Inductive Safe (System: Set) (Context: Set) (sys: System) 
                     (safety: System -> Context -> Prop) : Prop := 
  satisfiesSafetyRequirement:
    (forall cx: Context, safety sys cx) -> 
      Safe System Context sys safety.
