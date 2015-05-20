Inductive Sustainable (System: Set) (Context: Set) (sys: System) 
                              (sustainability: System -> Context -> Prop) : Prop := 
  mk_sustainability:
    (forall cx: Context, sustainability sys cx) -> 
      Sustainable System Context sys sustainability.