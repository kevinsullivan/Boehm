Inductive KeyPersonnel (System: Set) (Context: Set) (sys: System) 
                     (kp_cx: System -> Context -> Prop) : Prop := 
  mk_key_personnel:
    (forall cx: Context, kp_cx sys cx) -> 
      KeyPersonnel System Context sys kp_cx.