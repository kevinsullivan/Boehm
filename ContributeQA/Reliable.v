Inductive Reliable (System: Set) (Context: Set) (sys: System) 
                     (rl_cx: System -> Context -> Prop) : Prop := 
  mk_reliability:
    (forall cx: Context, rl_cx sys cx) -> 
      Reliable System Context sys rl_cx.