Inductive Robustness (System: Set) (Context: Set) (sys: System) 
                     (rob_cx: System -> Context -> Prop) : Prop := 
  mk_robustness:
    (forall cx: Context, rob_cx sys cx) -> 
      Robustness System Context sys rob_cx.