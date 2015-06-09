(** Maintainable General Theory *)

Inductive Maintainable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesMaintainabilityRequirement:
    (exists maintainable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, maintainable sys sh cx ps)) ->
    Maintainable System Stakeholder Context  Phase sys.
