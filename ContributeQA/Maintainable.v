Inductive Maintainable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (maintainable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesMaintainabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, maintainable sys sh cx ps) ->
      Maintainable System Stakeholder Context Phase sys maintainable.
