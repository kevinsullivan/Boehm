Inductive Manufacturable (System: Set) (Context: Set) (sys: System) 
                              (mf_cx: System -> Context -> Prop) : Prop := 
  mk_manufacturability:
    (forall cx: Context, mf_cx sys cx) -> 
      Manufacturable System Context sys mf_cx.