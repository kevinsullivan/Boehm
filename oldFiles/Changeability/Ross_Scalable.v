
Inductive Ross_Scalable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesRoss_ScalabilityRequirement: 
    (exists ross_scalable: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_scalable sys sh cx ps)) ->
    Ross_Scalable System Stakeholder Context Phase sys.