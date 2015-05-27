Inductive Reliable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (reliable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesReliabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, reliable sys sh cx ps) ->
      Reliable System Stakeholder Context Phase sys reliable.

