Inductive Impact (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                   (impact: System -> Stakeholder -> Context -> Phase -> Prop) : Prop :=
  mk_impact:
    (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, impact sys sh cx ps) ->
      Impact System Stakeholder Context Phase sys impact.
