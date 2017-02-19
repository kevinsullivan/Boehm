Require Export System.
Require Export Affordable.
Require Export Resilient.

(** Satisfactory *)
(** 
An instance of type [SystemType]  is satisfactory if, and only if,
 it is both [Affordable] and [Resilient].  These
system qualities are themselves composites of lower-level system
qualities, as detailed in their respective files.
*)

Inductive Satisfactory (sys_type: SystemType)
: Prop :=
  meetsSatisfactoryRequirementss:
    Affordable sys_type -> 
    Resilient sys_type -> 
    Satisfactory sys_type.

Hint Constructors
  (** Composite **)
  MissionEffective Dependable Flexible Efficient Affordable Resilient Satisfactory
  (** Contributing **)
  Adaptable PhysicalCapable CyberCapable HumanUsable Speed Endurable Maneuverable
  Accurate Impactful Scalable Versatile Interoperable Cost Duration KeyPersonnel OtherScarceResources
  Manufacturable Sustainable Secure Safe Reliable Maintainable Available Survivable Robust
  Modifiable Tailorable.