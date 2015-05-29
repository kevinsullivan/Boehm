(** Versatility General Theory *)

Inductive Versatile (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesVersatilityRequirement:
    (exists versatile: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, versatile sys sh cx ps)) ->
    Versatile System Stakeholder Context Phase sys.
