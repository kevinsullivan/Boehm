
Inductive ClassicalPassiveRobust (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (classicalPassiveRobust: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesClassicalPassiveRobustnessRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, classicalPassiveRobust sys sh cx ps) ->
      ClassicalPassiveRobust System Stakeholder Context Phase sys classicalPassiveRobust.