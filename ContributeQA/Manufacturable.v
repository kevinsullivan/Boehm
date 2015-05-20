Inductive Manufacturable (System: Set) (Context: Set) (sys: System) 
                              (manufacturability: System -> Context -> Prop) : Prop := 
  mk_manufacturability:
    (forall cx: Context, manufacturability sys cx) -> 
      Manufacturable System Context sys manufacturability.