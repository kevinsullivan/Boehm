Inductive HumanUsable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (humanUsable: System -> Stakeholder -> Context -> Prop) : Prop :=
  satisfiesHumanUsabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, humanUsable sys sh cx) ->
      HumanUsable System Stakeholder Context sys humanUsable.
