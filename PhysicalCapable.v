(** Physical Capable General Theory *)

Inductive PhysicalCapable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesPhysicalCapabilityRequirement:
    (exists physicalCapable: System -> Stakeholder -> Context -> Phase -> Prop, 
       (forall cx: Context,
        forall sh: Stakeholder,
        forall ps: Phase, physicalCapable sys sh cx ps)) ->
       PhysicalCapable System Stakeholder Context Phase sys.
