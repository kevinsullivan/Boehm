Inductive Versatile (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (versability: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_versatile:
    (forall cx: Context, forall sh: Stakeholder, versability sys sh cx) -> 
      Versatile System Stakeholder Context sys versability.