Inductive Tailorable (System: Set) (Context: Set) (sys: System) 
                     (tl_cx: System -> Context -> Prop) : Prop :=
  mk_tailorability:
    (forall cx: Context, tl_cx sys cx) -> 
      Tailorable System Context sys tl_cx.