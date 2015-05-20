Inductive Accurate (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (accuracy: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_accurate:
    (forall cx: Context, forall sh: Stakeholder, accuracy sys sh cx) -> 
      Accurate System Stakeholder Context sys accuracy.