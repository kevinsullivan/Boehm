Inductive Secure (System: Set) (Context: Set) (sys: System) 
                     (security: System -> Context -> Prop) : Prop := 
  mk_secure:
    (forall cx: Context, security sys cx) -> 
      Secure System Context sys security.