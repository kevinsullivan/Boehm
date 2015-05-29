(** *)

Inductive OtherScarceResources (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesOtherResoucesRequirement:
    (exists otherResources: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context,
        forall sh: Stakeholder,
        forall ps: Phase, otherResources sys sh cx ps)) ->
    OtherScarceResources System Stakeholder Context Phase sys.