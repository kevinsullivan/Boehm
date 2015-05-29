(** Maneuverable General Theory *)

Inductive Maneuverable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesManeuverabilityRequirement:
    (exists maneuverable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, maneuverable sys sh cx ps)) ->
    Maneuverable System Stakeholder Context Phase sys.