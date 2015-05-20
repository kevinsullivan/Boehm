Inductive Secure (System: Set) (Context: Set) (sys: System) 
                     (secure: System -> Context -> Prop) : Prop :=
  satisfiesSecurityRequirement:
    (forall cx: Context, secure sys cx) ->
      Secure System Context sys secure.
