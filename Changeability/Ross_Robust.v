
Inductive Ross_Robust (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (ross_robust: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesRoss_RobustnessRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_robust sys sh cx ps) ->
      Ross_Robust System Stakeholder Context Phase sys ross_robust.