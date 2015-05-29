(** Survivability General Theory *)

Inductive Survivable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesSurvivabilityRequirement:
    (exists survivable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, survivable sys sh cx ps)) ->
    Survivable System Stakeholder Context Phase sys.