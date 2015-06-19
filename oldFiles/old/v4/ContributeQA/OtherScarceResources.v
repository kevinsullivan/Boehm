Inductive OtherScarceResources (System: Set) (Context: Set) (sys: System) 
                     (osr_cx: System -> Context -> Prop) : Prop := 
  mk_other_scarce_resources:
    (forall cx: Context, osr_cx sys cx) -> 
      OtherScarceResources System Context sys osr_cx.