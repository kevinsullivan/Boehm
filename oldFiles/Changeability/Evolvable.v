
Inductive Evolvable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesEvolvabilityRequirement: 
    (exists evolvable: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, evolvable sys sh cx ps)) ->
    Evolvable System Stakeholder Context Phase sys.