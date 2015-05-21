Inductive PhysicalCapable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (physicalCapable: System -> Stakeholder -> Context -> Prop) : Prop :=
  satisfiesPhysicalCapabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, physicalCapable sys sh cx) ->
      PhysicalCapable System Stakeholder Context sys physicalCapable.
