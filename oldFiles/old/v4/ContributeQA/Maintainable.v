Inductive Maintainable (System: Set) (Context: Set) (sys: System) 
                     (mt_cx: System -> Context -> Prop) : Prop := 
  mk_maintainability:
    (forall cx: Context, mt_cx sys cx) -> 
      Maintainable System Context sys mt_cx.