Inductive KeyPersonnel (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (keyPersonnel: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesKeyPersonnelRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, keyPersonnel sys sh cx ps) ->
      KeyPersonnel System Stakeholder Context Phase sys keyPersonnel.
