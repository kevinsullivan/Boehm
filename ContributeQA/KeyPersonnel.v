(** Key Personnel General Theory *)

Inductive KeyPersonnel (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
   satisfiesKeyPersonnelRequirement:
     (exists keyPersonnel: System -> Stakeholder -> Context -> Phase -> Prop,
        (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, keyPersonnel sys sh cx ps)) ->
     KeyPersonnel System Stakeholder Context Phase sys.
