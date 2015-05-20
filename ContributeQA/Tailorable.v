Inductive Tailorable (System: Set) (Context: Set) (sys: System) 
                     (tailorability: System -> Context -> Prop) : Prop :=
  mk_tailorability:
    (forall cx: Context, tailorability sys cx) -> 
      Tailorable System Context sys tailorability.