Inductive Accurate (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (accurate: System -> Stakeholder -> Context -> Prop) : Prop :=
  satisfiesAccuracyRequirement:
    (forall cx: Context, forall sh: Stakeholder, accurate sys sh cx) ->
      Accurate System Stakeholder Context sys accurate.
