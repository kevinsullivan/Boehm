Inductive OtherScarceResources (System: Set) (Context: Set) (sys: System) 
                     (otherScareResources: System -> Context -> Prop) : Prop := 
  satisfiesOtherResoucesRequirement:
    (forall cx: Context, otherScareResources sys cx) -> 
      OtherScarceResources System Context sys otherScareResources.
