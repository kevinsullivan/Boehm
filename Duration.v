(** Duration General Theory *)

Inductive Duration (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesDurationRequirement:
    (exists duration: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, duration sys sh cx ps)) ->
    Duration System Stakeholder Context Phase sys.
