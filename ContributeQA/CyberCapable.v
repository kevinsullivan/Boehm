Inductive CyberCapable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (cyberCapable: System -> Stakeholder -> Context -> Prop) : Prop :=
  satisfiesCyberCapabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, cyberCapable sys sh cx) ->
      CyberCapable System Stakeholder Context sys cyberCapable.
