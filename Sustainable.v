(** Sustainability General Theory *)

Inductive Sustainable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesSustainabilityRequirement:
    (exists sustainable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, sustainable sys sh cx ps)) ->
    Sustainable System Stakeholder Context Phase sys.