(** HumanUsable General Theory *)

Inductive HumanUsable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesHumanUsabilityRequirement:
    (exists humanUsable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, humanUsable sys sh cx ps)) ->
    HumanUsable System Stakeholder Context Phase sys.

