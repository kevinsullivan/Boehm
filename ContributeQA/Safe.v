Inductive Safe (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
               (safe: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesSafetyRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, safe sys sh cx ps) ->
      Safe System Stakeholder Context Phase sys safe.
