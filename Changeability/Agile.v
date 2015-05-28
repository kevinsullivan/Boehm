
Inductive Agile (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (agile: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesAgilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, agile sys sh cx ps) ->
      Agile System Stakeholder Context Phase sys agile.