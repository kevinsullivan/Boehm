Inductive Duration (System: Set) (Context: Set) (sys: System) 
                     (duration: System -> Context -> Prop) : Prop := 
  mk_duration:
    (forall cx: Context, duration sys cx) -> 
      Duration System Context sys duration.