Inductive Accurate (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (accurate: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesAccuracyRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, accurate sys sh cx ps) ->
      Accurate System Stakeholder Context Phase sys accurate.
