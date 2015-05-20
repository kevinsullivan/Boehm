Inductive Endurable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (endurable: System -> Stakeholder -> Context -> Prop) : Prop :=
  satisfiesEndurabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, endurable sys sh cx) ->
      Endurable System Stakeholder Context sys endurable.
