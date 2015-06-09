(** Modifiable General Theory *)

(**
In Boehm's taxonomy, modifiable means that someone can change the
system structure or state can be changed to meet new needs.
*)

Inductive Modifiable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
 : Prop :=
  satisfiesModifiabilityRequirement:
                   (exists modifiable: System -> Stakeholder -> Context -> Phase -> Prop,
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, modifiable sys sh cx ps)) ->
      Modifiable System Stakeholder Context Phase sys.
