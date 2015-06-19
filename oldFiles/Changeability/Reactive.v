
Inductive Reactive (System: Set)  (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  satisfiesReactivityRequirement: 
    (exists reactive: System -> Stakeholder -> Context  -> Phase -> Prop,
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, reactive sys sh cx ps)) ->
      Reactive System Stakeholder Context Phase sys.