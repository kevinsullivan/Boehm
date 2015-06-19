Inductive Modifiable (System: Set) (Context: Set) (sys: System) 
                     (md_cx: System -> Context -> Prop) : Prop :=
  mk_modifiability:
    (forall cx: Context, md_cx sys cx) -> 
      Modifiable System Context sys md_cx.