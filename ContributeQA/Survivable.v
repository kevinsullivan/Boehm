Inductive Survivable (System: Set) (Context: Set) (sys: System) 
                     (survivability: System -> Context -> Prop) : Prop := 
  mk_survivability:
    (forall cx: Context, survivability sys cx) -> 
      Survivable System Context sys survivability.