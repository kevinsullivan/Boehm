Inductive Available (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                     (available: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesAvailabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, available sys sh cx ps) ->
      Available System Stakeholder Context Phase sys available.
