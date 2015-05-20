Inductive Scalable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (scalable: System -> Stakeholder -> Context -> Prop) : Prop :=
  satisfiesScalabilityRequirement:
    (forall cx: Context, forall sh: Stakeholder, scalable sys sh cx) ->
      Scalable System Stakeholder Context sys scalable.
