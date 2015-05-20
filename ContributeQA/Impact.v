Inductive Impact (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (impact: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_impact:
    (forall cx: Context, forall sh: Stakeholder, impact sys sh cx) -> 
      Impact System Stakeholder Context sys impact.