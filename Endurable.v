(** Endurable General Theory *)

Inductive Endurable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesEndurabilityRequirement:
    (exists endurable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, endurable sys sh cx ps)) ->
    Endurable System Stakeholder Context Phase sys.
