(** * Example -- Smart Home *)

(**
Kevin Sullivan, Koleman Nix, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 
*)

Require Export Satisfactory.

(*
Require Import MissionEffective Dependable Flexible Changeable Efficient Affordable Resilient
        Adaptable PhysicalCapable CyberCapable HumanUsable Speed Endurable Maneuverable
        Accurate Impactful Scalable Versatile Interoperable Cost Duration KeyPersonnel OtherScarceResources
        Manufacturable Sustainable Secure Safe Reliable Maintainable Available Survivable Robust
        Modifiable Tailorable.
*)

Definition Smart_Home_System := Datatypes.unit.
Inductive Smart_Home_Stakeholder := investor | end_user | developer | maintainer | public.
Inductive Smart_Home_Context := normal.
Inductive Smart_Home_Phase := phase1 | phase2.

(* 
Define relations (callback functions for Satisfactory class) to check a given system has corresponding quality.
We formalize the property that "a system can control the furnace on/off switch", with a trivial proof.
 *)
Inductive systemCanControlFurnaceOnOffSwitch: Smart_Home_System -> Prop := 
  systemCanControlFurnaceOnOffSwitch_proof: 
    forall s: Smart_Home_System, systemCanControlFurnaceOnOffSwitch s.

Inductive systemCanControlGarageDoorOpener: Smart_Home_System -> Prop :=
  systemCanControlGarageDoorOpener_proof: 
    forall s: Smart_Home_System, systemCanControlGarageDoorOpener s.

Hint Constructors systemCanControlFurnaceOnOffSwitch systemCanControlGarageDoorOpener.

Inductive physicalCapability 
  (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop := 
    physicalCapability_proof: systemCanControlFurnaceOnOffSwitch sys /\ 
    systemCanControlGarageDoorOpener sys -> 
      physicalCapability sys sh cx ps.

Inductive adaptability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    adaptability_proof: adaptability sys sh cx ps.

Inductive cyberCapability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    cyberCapability_proof: cyberCapability sys sh cx ps.

Inductive humanUsability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    humanUsability_proof: humanUsability sys sh cx ps.

(* We formalize the property that "a system is responsive", with a trivial proof. *)

Inductive systemIsResponsive : Smart_Home_System -> Prop :=
  systemIsResponsive_proof: forall sys: Smart_Home_System, systemIsResponsive sys.

Hint Constructors systemIsResponsive.

Inductive speed (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    speed_proof: systemIsResponsive sys -> speed sys sh cx ps.

Inductive endurability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    endurability_proof: endurability sys sh cx ps.

Inductive maneuverability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    maneuverability_proof: maneuverability sys sh cx ps.

Inductive accuracy (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    accuracy_proof: accuracy sys sh cx ps.

Inductive impact (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    impact_proof: impact sys sh cx ps.

Inductive scalability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    scalability_proof: scalability sys sh cx ps.

Inductive versatility (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    versatility_proof: versatility sys sh cx ps.

(* 
We formalize the properties that "a system can Work well with other systems 
(e.g., HVAC systems), and can be accessed from other systems (pc, car, phone)", 
with trivial proofs.
*)

Inductive systemCanWorkWithOtherSystems: Smart_Home_System -> Prop := 
  systemCanWorkWithOtherSystems_proof: 
    forall sys: Smart_Home_System, systemCanWorkWithOtherSystems sys.

Inductive systemCanBeAccessedFromOtherSystems: Smart_Home_System -> Prop :=
  systemCanBeAccessedFromOtherSystems_proof: forall sys: Smart_Home_System, 
    systemCanBeAccessedFromOtherSystems sys.

Hint Constructors systemCanWorkWithOtherSystems systemCanBeAccessedFromOtherSystems.

Inductive interoperability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    interoperability_proof: 
      systemCanWorkWithOtherSystems sys /\ 
      systemCanBeAccessedFromOtherSystems sys -> 
        interoperability sys sh cx ps.

Inductive cost (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    cost_proof: cost sys sh cx ps.

Inductive duration (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    duration_proof: duration sys sh cx ps.

Inductive keyPersonnel (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    keyPersonnel_proof: keyPersonnel sys sh cx ps.

Inductive otherScarceResources (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    otherScareResources_proof: otherScarceResources sys sh cx ps.

Inductive manufacturability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    manufacturability_proof: manufacturability sys sh cx ps.

Inductive sustainability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    sustainability_proof: sustainability sys sh cx ps.

(* 
We formalize the properties that "a system is difficult to hack, and does not put 
the owners of the home in danger.", with trivial proofs.
 *)

Inductive systemIsDifficultToHack: Smart_Home_System -> Prop :=
  systemIsDifficultToHack_proof: forall sys: Smart_Home_System, 
    systemIsDifficultToHack sys.

Inductive systemDoesNotHarmOwners: Smart_Home_System -> Prop :=
  systemDoesNotHarmOwners_proof: forall sys: Smart_Home_System, 
    systemDoesNotHarmOwners sys.

Hint Constructors systemIsDifficultToHack systemDoesNotHarmOwners.

Inductive security (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    security_proof: 
      systemIsDifficultToHack sys /\ 
      systemDoesNotHarmOwners sys -> 
        security sys sh cx ps.

Inductive safety (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    safety_proof: safety sys sh cx ps.

Inductive reliability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    reliability_proof: reliability sys sh cx ps.

Inductive maintainability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    maintainability_proof: maintainability sys sh cx ps.

Inductive availability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    availability_proof: availability sys sh cx ps.

Inductive survivability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    survivability_proof: survivability sys sh cx ps.

Inductive robustness (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    robustness_proof: robustness sys sh cx ps.

Inductive modifiability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    modifiability_proof: modifiability sys sh cx ps.

Inductive tailorability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    tailorability_proof: tailorability sys sh cx ps.

Inductive changeability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) 
  (cx: Smart_Home_Context) (ps: Smart_Home_Phase): Prop :=
    changeability_proof: changeability sys sh cx ps.

(* We define an instance of Satisfactory for a smart home project.*)
Instance Smart_Home_Instance: Satisfactory Smart_Home_System Smart_Home_Stakeholder Smart_Home_Context Smart_Home_Phase tt := {}.
Hint Constructors
     (** Composite **)
     MissionEffective Dependable Flexible Changeable Efficient Affordable Resilient
     (** Contributing **)
     Adaptable PhysicalCapable CyberCapable HumanUsable Speed Endurable Maneuverable
     Accurate Impactful Scalable Versatile Interoperable Cost Duration KeyPersonnel OtherScarceResources
     Manufacturable Sustainable Secure Safe Reliable Maintainable Available Survivable Robust
     Modifiable Tailorable
     adaptability physicalCapability cyberCapability humanUsability speed endurability maneuverability
     accuracy impact scalability versatility interoperability cost duration keyPersonnel otherScarceResources
     manufacturability sustainability security safety reliability maintainability
     availability survivability robustness modifiability tailorability changeability.

(* 
If the instance can be proved, then we show the given system has all required qualities.
If we cannot find proofs of this instance, then we can conclude that the system is not accepted. 
 *)
Proof.
  (* affordable *)
  constructor.
    (* mission effective *)
    constructor.
        constructor. exists physicalCapability. auto. 
        constructor. exists cyberCapability. auto.
        constructor. exists humanUsability. auto.
        constructor. exists speed. auto.
        constructor. exists endurability. auto.
        constructor. exists maneuverability. auto.
        constructor. exists accuracy. auto.
        constructor. exists impact. auto.
        constructor. exists scalability. auto.
        constructor. exists versatility. auto.
        constructor. exists interoperability. auto.
    (* efficient *)
    constructor.
        constructor. exists cost. auto.
        constructor. exists duration. auto.
        constructor. exists keyPersonnel. auto.
        constructor. exists otherScarceResources. auto.
        constructor. exists manufacturability. auto.
        constructor. exists sustainability. auto.
  (* resilient *)
  constructor.
    (* dependable *)
    constructor.
      constructor. exists security. auto.
      constructor. exists safety. auto.
      constructor. exists reliability. auto.
      constructor. exists maintainability. auto.
      constructor. exists availability. auto.
      constructor. exists survivability. auto.
      constructor. exists robustness. auto.
    (* flexible *)
    constructor.
      constructor. exists modifiability. auto.
      constructor. exists tailorability. auto.
      constructor. exists adaptability. auto.
    (* changeable *)
    constructor. exists changeability. auto. 
Qed.
