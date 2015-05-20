Inductive Endurable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (endurability: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_endurable:
    (forall cx: Context, forall sh: Stakeholder, endurability sys sh cx) -> 
      Endurable System Stakeholder Context sys endurability.