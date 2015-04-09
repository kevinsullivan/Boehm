Inductive Endurable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (ed_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_endurable:
    (forall cx: Context, forall sh: Stakeholder, ed_sh_cx sys sh cx) -> 
      Endurable System Stakeholder Context sys ed_sh_cx.