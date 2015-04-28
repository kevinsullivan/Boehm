Inductive Cost (System: Set) (Context: Set) (sys: System) 
                     (cs_cx: System -> Context -> Prop) : Prop := 
  mk_cost:
    (forall cx: Context, cs_cx sys cx) -> 
      Cost System Context sys cs_cx.