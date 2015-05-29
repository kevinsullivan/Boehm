(** Security General Theory *)

Inductive Secure (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesSecurityRequirement:
    (exists secure: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, secure sys sh cx ps)) ->
    Secure System Stakeholder Context Phase sys.
