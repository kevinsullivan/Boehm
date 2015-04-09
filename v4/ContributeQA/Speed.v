Inductive Speed (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (sp_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_speed:
    (forall cx: Context, forall sh: Stakeholder, sp_sh_cx sys sh cx) -> 
      Speed System Stakeholder Context sys sp_sh_cx.