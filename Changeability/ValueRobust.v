
Inductive ValueRobust (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesValueRobustnessRequirement: 
    (exists valueRobust: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, valueRobust sys sh cx ps)) ->
     ValueRobust System Stakeholder Context Phase sys.