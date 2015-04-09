Inductive Adaptable (System: Set) (Context: Set) (sys: System) 
                     (adp_cx: System -> Context -> Prop) : Prop :=
  mk_adaptability:
    (forall cx: Context, adp_cx sys cx) -> 
      Adaptable System Context sys adp_cx.