(** Modifiable General Theory *)

Inductive Modifiable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
 : Prop :=
  satisfiesModifiabilityRequirement:
                   (exists modifiable: System -> Stakeholder -> Context -> Phase -> Prop,
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, modifiable sys sh cx ps)) ->
      Modifiable System Stakeholder Context Phase sys.
