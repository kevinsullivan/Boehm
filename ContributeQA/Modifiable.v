Inductive Modifiable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (modifiable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesModifiabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, modifiable sys sh cx ps) ->
      Modifiable System Stakeholder Context Phase sys modifiable.
