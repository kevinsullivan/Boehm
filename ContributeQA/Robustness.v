Inductive Robustness (System: Set) (Context: Set) (sys: System) 
                     (robust: System -> Context -> Prop) : Prop :=
  satisfiesRobustnessRequirement:
    (forall cx: Context, robust sys cx) ->
      Robustness System Context sys robust.
