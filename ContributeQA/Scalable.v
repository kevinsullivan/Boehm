Inductive Scalable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (scalability: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_scalable:
    (forall cx: Context, forall sh: Stakeholder, scalability sys sh cx) -> 
      Scalable System Stakeholder Context sys scalability.