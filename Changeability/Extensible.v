
Inductive Extensible (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (extensible: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesextensibilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, extensible sys sh cx ps) ->
      Extensible System Stakeholder Context Phase sys extensible.