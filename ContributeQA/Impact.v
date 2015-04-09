Inductive Impact (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (ip_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_impact:
    (forall cx: Context, forall sh: Stakeholder, ip_sh_cx sys sh cx) -> 
      Impact System Stakeholder Context sys ip_sh_cx.