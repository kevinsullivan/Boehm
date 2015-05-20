Inductive Reliable (System: Set) (Context: Set) (sys: System) 
                     (reliability: System -> Context -> Prop) : Prop := 
  mk_reliability:
    (forall cx: Context, reliability sys cx) -> 
      Reliable System Context sys reliability.