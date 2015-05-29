Inductive Available (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesAvailabilityRequirement:
    (exists available: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, available sys sh cx ps)) ->
    Available System Stakeholder Context Phase sys.
