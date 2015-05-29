(** Cost General Theory *)

Inductive Cost (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System)
: Prop :=
  satisfiesCostRequirement:
    (exists cost: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, cost sys sh cx ps)) ->
       Cost System Stakeholder Context Phase sys.

