Inductive PhysicalCapable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (physicalCapable: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesPhysicalCapabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, physicalCapable sys sh cx ps) ->
      PhysicalCapable System Stakeholder Context Phase sys physicalCapable.
