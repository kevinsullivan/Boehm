Inductive Scalable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesScalabilityRequirement:
    (exists scalable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, scalable sys sh cx ps)) ->
    Scalable System Stakeholder Context Phase sys.