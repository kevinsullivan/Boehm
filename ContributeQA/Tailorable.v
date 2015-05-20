Inductive Tailorable (System: Set) (Context: Set) (sys: System) 
                     (tailorable: System -> Context -> Prop) : Prop :=
  satisfiesTailorabilityRequirement:
    (forall cx: Context, tailorable sys cx) ->
      Tailorable System Context sys tailorable.
