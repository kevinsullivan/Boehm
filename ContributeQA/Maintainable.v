Inductive Maintainable (System: Set) (Context: Set) (sys: System) 
                     (maintainability: System -> Context -> Prop) : Prop := 
  mk_maintainability:
    (forall cx: Context, maintainability sys cx) -> 
      Maintainable System Context sys maintainability.