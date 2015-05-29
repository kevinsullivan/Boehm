(** Speed General Theory *)

Inductive Speed (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesSpeedRequirement:
    (exists speed: System -> Stakeholder -> Context -> Phase -> Prop, 
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, speed sys sh cx ps)) ->
       Speed System Stakeholder Context Phase sys.
