(** Impact General Theory *)

Inductive Impact (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  mk_impact:
    (exists impact: System -> Stakeholder -> Context -> Phase -> Prop, 
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, impact sys sh cx ps)) ->
    Impact System Stakeholder Context Phase sys.
