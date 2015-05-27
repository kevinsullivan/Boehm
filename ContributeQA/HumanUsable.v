Inductive HumanUsable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (humanUsable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesHumanUsabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, humanUsable sys sh cx ps) ->
      HumanUsable System Stakeholder Context Phase sys humanUsable.

