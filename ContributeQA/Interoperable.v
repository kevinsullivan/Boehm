Inductive Interoperable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (interoperability: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_interoperable:
    (forall cx: Context, forall sh: Stakeholder, interoperability sys sh cx) -> 
      Interoperable System Stakeholder Context sys interoperability.