
Inductive Agile (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) : Prop :=
  satisfiesAgilityRequirement:
     (exists agile: System -> Stakeholder -> Context  -> Phase -> Prop,  
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, agile sys sh cx ps)) ->
     Agile System Stakeholder Context Phase sys.