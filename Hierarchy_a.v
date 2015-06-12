(** Leaf Properties*)

Inductive Accurate  (sys: System) : Prop :=
  satisfiesAccuracyRequirement:
    (exists accurate: System -> Prop, accurate sys) -> Accurate sys.

Inductive Adaptable  (sys: System) : Prop :=
  satisfiesAdaptabilityRequirement:
    (exists adaptable: System -> Prop, adaptable sys) -> Adaptable sys.

Inductive Affordable (sys: System): Prop :=
  satisfiesAffordabilityPrerequisites: 
    MissionEffective sys ->
    Efficient sys ->
    Affordable sys.

Inductive Cost (sys: System) : Prop :=
  satisfiesCostRequirement:
    (exists cost: System -> Prop, cost sys) -> Cost sys.

Inductive CyberCapable (sys: System) : Prop :=
  satisfiesCyberCapabilityRequirement:
    (exists cyberCapable: System -> Prop, cyberCapable sys) -> CyberCapable sys.

