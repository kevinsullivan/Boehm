
Inductive Extensible (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesextensibilityRequirement: 
     (exists extensible: System -> Stakeholder -> Context  -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, extensible sys sh cx ps)) ->
     Extensible System Stakeholder Context Phase sys.