Inductive CyberCapable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (cyberCapability: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_cyber_capable:
    (forall cx: Context, forall sh: Stakeholder, cyberCapability sys sh cx) -> 
      CyberCapable System Stakeholder Context sys cyberCapability.