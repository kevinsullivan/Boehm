Inductive Available (System: Set) (Context: Set) (sys: System) 
                     (avl_cx: System -> Context -> Prop) : Prop := 
  mk_availability:
    (forall cx: Context, avl_cx sys cx) -> 
      Available System Context sys avl_cx.