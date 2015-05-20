Inductive Modifiable (System: Set) (Context: Set) (sys: System) 
                     (modifiability: System -> Context -> Prop) : Prop :=
  mk_modifiability:
    (forall cx: Context, modifiability sys cx) -> 
      Modifiable System Context sys modifiability.