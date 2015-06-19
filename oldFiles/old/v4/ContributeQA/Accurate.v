Inductive Accurate (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (ac_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_accurate:
    (forall cx: Context, forall sh: Stakeholder, ac_sh_cx sys sh cx) -> 
      Accurate System Stakeholder Context sys ac_sh_cx.