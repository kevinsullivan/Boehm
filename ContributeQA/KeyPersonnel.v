Inductive KeyPersonnel (System: Set) (Context: Set) (sys: System) 
                     (keyPersonnel: System -> Context -> Prop) : Prop := 
  satisfiesKeyPersonnelRequirement:
    (forall cx: Context, keyPersonnel sys cx) -> 
      KeyPersonnel System Context sys keyPersonnel.
