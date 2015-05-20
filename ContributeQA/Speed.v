Inductive Speed (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (speed: System -> Stakeholder -> Context -> Prop) : Prop := 
  satisfiesSpeedRequirement:
    (forall cx: Context, forall sh: Stakeholder, speed sys sh cx) -> 
      Speed System Stakeholder Context sys speed.
