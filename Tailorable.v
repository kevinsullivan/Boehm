(** Tailorability General Theory *)

Inductive Tailorable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesTailorabilityRequirement:
    (exists tailorable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, tailorable sys sh cx ps)) ->
       Tailorable System Stakeholder Context Phase sys.