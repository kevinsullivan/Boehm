Inductive Secure (System: Set) (Context: Set) (sys: System) 
                     (sec_cx: System -> Context -> Prop) : Prop := 
  mk_secure:
    (forall cx: Context, sec_cx sys cx) -> 
      Secure System Context sys sec_cx.