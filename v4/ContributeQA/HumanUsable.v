Inductive HumanUsable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (hu_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_human_usable:
    (forall cx: Context, forall sh: Stakeholder, hu_sh_cx sys sh cx) -> 
      HumanUsable System Stakeholder Context sys hu_sh_cx.