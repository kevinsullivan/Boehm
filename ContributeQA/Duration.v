
Inductive Duration (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (duration: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesDurationRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, duration sys sh cx ps) ->
      Duration System Stakeholder Context Phase sys duration.
