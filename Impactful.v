(** Impact General Theory *)

Inductive Impactful (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesImpactRequirement:
    (exists impactful: System -> Stakeholder -> Context -> Phase -> Prop, 
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, impactful sys sh cx ps)) ->
    Impactful System Stakeholder Context Phase sys.
