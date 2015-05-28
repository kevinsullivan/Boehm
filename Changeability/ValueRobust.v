
Inductive ValueRobust (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (valueRobust: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesValueRobustnessRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, valueRobust sys sh cx ps) ->
      ValueRobust System Stakeholder Context Phase sys valueRobust.