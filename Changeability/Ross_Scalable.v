
Inductive Ross_Scalable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                                (ross_scalable: System -> Stakeholder -> Context  -> Phase -> Prop) : Prop :=
  satisfiesRoss_ScalabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_scalable sys sh cx ps) ->
      Ross_Scalable System Stakeholder Context Phase sys ross_scalable.