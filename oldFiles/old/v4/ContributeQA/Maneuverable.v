Inductive Maneuverable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (mv_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_maneuverable:
    (forall cx: Context, forall sh: Stakeholder, mv_sh_cx sys sh cx) -> 
      Maneuverable System Stakeholder Context sys mv_sh_cx.