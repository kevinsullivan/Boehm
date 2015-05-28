
Inductive Ross_Modifiable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (ross_modifiable: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesRoss_ModifiabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_modifiable sys sh cx ps) ->
      Ross_Modifiable System Stakeholder Context Phase sys ross_modifiable.