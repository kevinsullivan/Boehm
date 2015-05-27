Inductive Secure (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (secure: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  satisfiesSecurityRequirement:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, secure sys sh cx ps) ->
      Secure System Stakeholder Context Phase sys secure.