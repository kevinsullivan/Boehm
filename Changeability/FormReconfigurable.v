
Inductive FormReconfigurable (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesFormReconfigurabilityRequirement: 
    (exists formReconfigurable: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, formReconfigurable sys sh cx ps)) ->
    FormReconfigurable System Stakeholder Context Phase sys.