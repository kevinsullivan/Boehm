Inductive Safe (System: Set) (Context: Set) (sys: System) 
                     (safety: System -> Context -> Prop) : Prop := 
  mk_safe:
    (forall cx: Context, safety sys cx) -> 
      Safe System Context sys safety.