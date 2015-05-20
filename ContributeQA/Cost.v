Inductive Cost (System: Set) (Context: Set) (sys: System) 
                     (cost: System -> Context -> Prop) : Prop := 
  mk_cost:
    (forall cx: Context, cost sys cx) -> 
      Cost System Context sys cost.