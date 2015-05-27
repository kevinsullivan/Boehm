Inductive Speed (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (speed: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesSpeedRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, speed sys sh cx ps) ->
      Speed System Stakeholder Context Phase sys speed.
