(* CyberCapable General Theory *)
Require Export System.

Inductive CyberCapable {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesCyberCapabilityRequirement:
    (exists cyberCapable: System msys -> Prop, cyberCapable sys) -> CyberCapable sys.
