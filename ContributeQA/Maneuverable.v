Inductive Maneuverable (System: Set) (Stakeholder: Set) (Context: Set) (sys: System) 
                     (maneuverability: System -> Stakeholder -> Context -> Prop) : Prop := 
  mk_maneuverable:
    (forall cx: Context, forall sh: Stakeholder, maneuverability sys sh cx) -> 
      Maneuverable System Stakeholder Context sys maneuverability.