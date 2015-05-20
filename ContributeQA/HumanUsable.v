Inductive HumanUsable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (humanUsability: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_human_usable:
    (forall cx: Context, forall sh: Stakeholder, humanUsability sys sh cx) -> 
      HumanUsable System Stakeholder Context sys humanUsability.