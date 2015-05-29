(** Manufacturable General Theory *)

Inductive Manufacturable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesManufacturabilityRequirement:
    (exists manufacturable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, manufacturable sys sh cx ps)) ->
    Manufacturable System Stakeholder Context Phase sys.