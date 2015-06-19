
Inductive Ross_Modifiable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesRoss_ModifiabilityRequirement: 
    (exists ross_modifiable: System -> Stakeholder -> Context  -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, ross_modifiable sys sh cx ps)) ->
    Ross_Modifiable System Stakeholder Context Phase sys.