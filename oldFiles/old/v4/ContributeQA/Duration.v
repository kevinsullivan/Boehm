Inductive Duration (System: Set) (Context: Set) (sys: System) 
                     (dr_cx: System -> Context -> Prop) : Prop := 
  mk_duration:
    (forall cx: Context, dr_cx sys cx) -> 
      Duration System Context sys dr_cx.