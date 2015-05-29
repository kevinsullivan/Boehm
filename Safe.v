(** Safety General Theory *)

Inductive Safe (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesSafetyRequirement:
    (exists safe: System -> Stakeholder -> Context -> Phase -> Prop, 
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, safe sys sh cx ps)) ->
    Safe System Stakeholder Context Phase sys.
