(* CyberCapable General Theory *)

Inductive CyberCapable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
: Prop :=
  satisfiesCyberCapabilityRequirement:
    (exists cyberCapable: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, cyberCapable sys sh cx ps)) ->
    CyberCapable System Stakeholder Context Phase sys.
