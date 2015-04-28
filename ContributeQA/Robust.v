Inductive Robust (System: Set) (Context: Set) (sys: System) 
                     (rob_cx: System -> Context -> Prop) : Prop := 
  mk_robustness:
    (forall cx: Context, rob_cx sys cx) -> 
      Robust System Context sys rob_cx.