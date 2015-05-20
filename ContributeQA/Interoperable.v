Inductive Interoperable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (interoperable: System -> Stakeholder -> Context -> Prop) : Prop :=
  satisfiesInteroperabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, interoperable sys sh cx) ->
      Interoperable System Stakeholder Context sys interoperable.
