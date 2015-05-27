Inductive Robustness (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (robust: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesRobustnessRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, robust sys sh cx ps) ->
      Robustness System Stakeholder Context Phase sys robust.
