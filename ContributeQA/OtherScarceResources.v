Inductive OtherScarceResources (System: Set) (Context: Set) (sys: System) 
                     (otherScareResources: System -> Context -> Prop) : Prop := 
  mk_other_scarce_resources:
    (forall cx: Context, otherScareResources sys cx) -> 
      OtherScarceResources System Context sys otherScareResources.