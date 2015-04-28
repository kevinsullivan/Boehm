Inductive Scalable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (sc_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_scalable:
    (forall cx: Context, forall sh: Stakeholder, sc_sh_cx sys sh cx) -> 
      Scalable System Stakeholder Context sys sc_sh_cx.