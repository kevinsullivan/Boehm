Inductive CyberCapable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (cc_sh_cx: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_cyber_capable:
    (forall cx: Context, forall sh: Stakeholder, cc_sh_cx sys sh cx) -> 
      CyberCapable System Stakeholder Context sys cc_sh_cx.