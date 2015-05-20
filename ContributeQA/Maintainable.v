Inductive Maintainable (System: Set) (Context: Set) (sys: System) 
                     (maintainable: System -> Context -> Prop) : Prop :=
  satisfiesMaintainabilityRequirement:
    (forall cx: Context, maintainable sys cx) ->
      Maintainable System Context sys maintainable.
