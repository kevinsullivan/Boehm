Inductive Maneuverable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (maneuverable: System -> Stakeholder -> Context -> Prop) : Prop :=
  satisfiesManeuverabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, maneuverable sys sh cx) ->
      Maneuverable System Stakeholder Context sys maneuverable.
