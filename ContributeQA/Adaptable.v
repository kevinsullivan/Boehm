(** Adaptable General Theory *)

Inductive Adaptable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                      : Prop :=
  satisfiesAdaptabilityRequirement:
(exists adaptable: System -> Stakeholder -> Context -> Phase -> Prop,
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, adaptable sys sh cx ps)) ->
      Adaptable System Stakeholder Context Phase sys.


