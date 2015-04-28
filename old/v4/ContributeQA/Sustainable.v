Inductive Sustainable (System: Set) (Context: Set) (sys: System) 
                              (sust_cx: System -> Context -> Prop) : Prop := 
  mk_sustainability:
    (forall cx: Context, sust_cx sys cx) -> 
      Sustainable System Context sys sust_cx.