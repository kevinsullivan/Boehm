Inductive OtherScarceResources (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (otherScareResources: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesOtherResoucesRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, otherScareResources sys sh cx ps) ->
      OtherScarceResources System Stakeholder Context Phase sys otherScareResources.