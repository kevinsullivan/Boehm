(** Robustness General Theory *)

Inductive Robust (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesRobustnessRequirement:
    (exists robust: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, robust sys sh cx ps)) ->
    Robust System Stakeholder Context Phase sys.
