(** Adaptable General Theory *)

(**
In Boehm's taxonomy, adaptable means that a system can change its
state or behavior (and maybe in the future its structure) to improve its
fitness for purpose. Adapable here really means self-adapting.
*)

Inductive Adaptable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System)
                      : Prop :=
  satisfiesAdaptabilityRequirement:
(exists adaptable: System -> Stakeholder -> Context -> Phase -> Prop,
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, adaptable sys sh cx ps)) ->
      Adaptable System Stakeholder Context Phase sys.
