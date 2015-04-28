Inductive Survivable (System: Set) (Context: Set) (sys: System) 
                     (svv_cx: System -> Context -> Prop) : Prop := 
  mk_survivability:
    (forall cx: Context, svv_cx sys cx) -> 
      Survivable System Context sys svv_cx.