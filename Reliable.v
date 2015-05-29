(** Reliability General Theory *)

Inductive Reliable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesReliabilityRequirement:
    (exists reliable: System -> Stakeholder -> Context -> Phase -> Prop, 
      (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, reliable sys sh cx ps)) ->
    Reliable System Stakeholder Context Phase sys.

