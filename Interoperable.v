(** Interoperable General Theory *)

Inductive Interoperable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesInteroperabilityRequirement:
    (exists interoperable: System -> Stakeholder -> Context -> Phase -> Prop, 
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, interoperable sys sh cx ps)) ->
    Interoperable System Stakeholder Context Phase sys.
