Inductive PhysicalCapable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (pc_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_physical_capable:
    (forall cx: Context, forall sh: Stakeholder, pc_sh_cx sys sh cx) -> 
      PhysicalCapable System Stakeholder Context sys pc_sh_cx.