Inductive Interoperable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (interoperable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesInteroperabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, interoperable sys sh cx ps) ->
      Interoperable System Stakeholder Context Phase sys interoperable.
