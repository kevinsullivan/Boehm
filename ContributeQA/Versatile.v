Inductive Versatile (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (vs_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_versatile:
    (forall cx: Context, forall sh: Stakeholder, vs_sh_cx sys sh cx) -> 
      Versatile System Stakeholder Context sys vs_sh_cx.