Inductive Available (System: Set) (Context: Set) (sys: System) 
                     (availability: System -> Context -> Prop) : Prop := 
  satisfiesAvailabilityRequirement:
    (forall cx: Context, availability sys cx) -> 
      Available System Context sys availability.
