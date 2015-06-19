Inductive Safe (System: Set) (Context: Set) (sys: System) 
                     (sf_cx: System -> Context -> Prop) : Prop := 
  mk_safe:
    (forall cx: Context, sf_cx sys cx) -> 
      Safe System Context sys sf_cx.