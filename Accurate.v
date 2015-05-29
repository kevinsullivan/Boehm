(** Accuracy General Theory *)

Inductive Accurate (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesAccuracyRequirement:
    (exists accurate: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, accurate sys sh cx ps)) ->
    Accurate System Stakeholder Context Phase sys.
