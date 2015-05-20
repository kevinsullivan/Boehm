(** * Example -- Smart Home *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

May, 2015
*)
Add Rec LoadPath "./ContributeQA".
Require Import Satisfactory.
Require Import Changeable.

Definition Smart_Home_System := Datatypes.unit.
Inductive Smart_Home_Stakeholder := investor | end_user | developer | maintainer | public.
Inductive Smart_Home_Context := normal.

(* 
Define relations (callback functions for Satisfactory class) to check a given system has corresponding quality.
We formalize the property that "a system can control the furnace on/off switch", with a trivial proof.
*)
Inductive systemCanControlFurnaceOnOffSwitch: Smart_Home_System -> Prop := 
  systemCanControlFurnaceOnOffSwitch_proof: forall s: Smart_Home_System, systemCanControlFurnaceOnOffSwitch s.

Inductive systemCanControlGarageDoorOpener: Smart_Home_System -> Prop :=
  systemCanControlGarageDoorOpener_proof: forall s: Smart_Home_System, systemCanControlGarageDoorOpener s.

Inductive physicalCapability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop := 
  physicalCapability_proof: systemCanControlFurnaceOnOffSwitch sys /\ systemCanControlGarageDoorOpener sys -> physicalCapability sys sh cx.

(* An adaptivity change statement.*)
Definition smart_home_system_adaptability_requirement : changeStatement := 
  mk_changeStatement 
    (perturbation_shift "some events")
    (context_circumstantial "some circumstantial contexts")
    phase_preOps 
    (agent_internal "aAgent")
    (mk_change direction_increase (parameter_level "aParameter") (origin_one "anOrginin") (destination_one "aDestination") aspect_function)
    (mechanism_description "some mechanism") 
    (mk_change direction_increase(parameter_level "anotherParameter") (origin_one "anotherOrginin") (destination_one "anotherDestination") aspect_function)
    (abstraction_architecture "anAbstraction")
    (valuable_compound "valuable because of" 
      (reaction_sooner_than 11 unit_time_second)
      (span_shorter_than 1 unit_time_day)
      (cost_less_than 100 unit_money_dollar)
      (benefit_same_as "keep power off")).

Inductive systemMeetsSpecificAdaptabilityRequirement: Smart_Home_System -> changeStatement -> Prop :=
  systemMeetsSpecificAdaptabilityRequirement_proof: 
    forall s: Smart_Home_System, forall c: changeStatement, 
      In adaptability (tipeAssignment c) -> systemMeetsSpecificAdaptabilityRequirement s c.

(* This is the relation that check a given system has adaptability quality.*)
Inductive adaptability (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  adaptability_proof: systemMeetsSpecificAdaptabilityRequirement sys smart_home_system_adaptability_requirement -> 
      adaptability sys cx.

Inductive cyberCapability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  cyberCapability_proof: cyberCapability sys sh cx.

Inductive humanUsability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  humanUsability_proof: humanUsability sys sh cx.

(* We formalize the property that "a system is responsive", with a trivial proof. *)

Inductive systemIsResponsive : Smart_Home_System -> Prop :=
  systemIsResponsive_proof: forall sys: Smart_Home_System, systemIsResponsive sys.

Inductive speed (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  speed_proof: systemIsResponsive sys -> speed sys sh cx.

Inductive endurability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  endurability_proof: endurability sys sh cx.

Inductive maneuverability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  maneuverability_proof: maneuverability sys sh cx.

Inductive accuracy (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  accuracy_proof: accuracy sys sh cx.

Inductive impact (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  impact_proof: impact sys sh cx.

Inductive scalability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  scalability_proof: scalability sys sh cx.

Inductive versability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  versability_proof: versability sys sh cx.

(* We formalize the properties that "a system can Works well with other systems (i.e. HVAC systems), 
   and can be accessed from other systems (pc, car, phone)", with trivial proofs.*)

Inductive systemCanWorkWithOtherSystems: Smart_Home_System -> Prop := 
  systemCanWorkWithOtherSystems_proof: forall sys: Smart_Home_System, systemCanWorkWithOtherSystems sys.

Inductive systemCanBeAccessedFromOtherSystems: Smart_Home_System -> Prop :=
  systemCanBeAccessedFromOtherSystems_proof: forall sys: Smart_Home_System, systemCanBeAccessedFromOtherSystems sys.

Inductive interoperability (sys: Smart_Home_System) (sh: Smart_Home_Stakeholder) (cx: Smart_Home_Context): Prop :=
  interoperability_proof: systemCanWorkWithOtherSystems sys /\ systemCanBeAccessedFromOtherSystems sys -> interoperability sys sh cx.

Inductive cost (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  cost_proof: cost sys cx.

Inductive duration (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  duration_proof: duration sys cx.

Inductive keyPersonnel (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  keyPersonnel_proof: keyPersonnel sys cx.

Inductive otherScareResources (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  otherScareResources_proof: otherScareResources sys cx.

Inductive manufacturability (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  manufacturability_proof: manufacturability sys cx.

Inductive sustainability (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  sustainability_proof: sustainability sys cx.

(* 
We formalize the properties that "a system is difficult to hack, and does not put the owners of the home in danger.", with trivial proofs.
*)

Inductive systemIsDifficultToHack: Smart_Home_System -> Prop :=
  systemIsDifficultToHack_proof: forall sys: Smart_Home_System, systemIsDifficultToHack sys.

Inductive systemDoesNotHarmOwners: Smart_Home_System -> Prop :=
  systemDoesNotHarmOwners_proof: forall sys: Smart_Home_System, systemDoesNotHarmOwners sys.

Inductive security (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  security_proof: systemIsDifficultToHack sys /\ systemDoesNotHarmOwners sys -> security sys cx.

Inductive safety (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  safety_proof: safety sys cx.

Inductive reliability (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  reliability_proof: reliability sys cx.

Inductive maintainability (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  maintainability_proof: maintainability sys cx.

Inductive availability (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  availability_proof: availability sys cx.

Inductive survivability (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  survivability_proof: survivability sys cx.

Inductive robustness (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  robustness_proof: robustness sys cx.

Inductive modifiability (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  modifiability_proof: modifiability sys cx.

Inductive tailorability (sys: Smart_Home_System) (cx: Smart_Home_Context): Prop :=
  tailorability_proof: tailorability sys cx.

(* We define an instance of Satisfactory for a smart home project.*)
Instance Smart_Home_Instance: Satisfactory Smart_Home_System Smart_Home_Stakeholder Smart_Home_Context := {
    sys := tt

  ; physicalCapability := physicalCapability
  ; cyberCapability := cyberCapability
  ; humanUsability := humanUsability
  ; speed:= speed
  ; endurability := endurability
  ; maneuverability := maneuverability
  ; accuracy := accuracy
  ; impact := impact
  ; scalability := scalability
  ; versability := versability
  ; interoperability := interoperability

  ; cost := cost
  ; duration := duration
  ; keyPersonnel := keyPersonnel
  ; otherScareResources := otherScareResources
  ; manufacturability := manufacturability
  ; sustainability := sustainability

  ; security := security
  ; safety := safety
  ; reliability := reliability
  ; maintainability := maintainability
  ; availability := availability
  ; survivability := survivability
  ; robustness := robustness

  ; modifiability := modifiability
  ; tailorability := tailorability
  ; adaptability := adaptability
}.

(* 
If the instance can be proved, then we show the given system has all required qualities.
If we cannot find proofs of this instance, then we can conclude that the system is not accepted. 
*)
Proof.
apply mk_mission_eff.
apply mk_physical_capable.
intros; apply physicalCapability_proof.
apply conj.
apply systemCanControlFurnaceOnOffSwitch_proof.
apply systemCanControlGarageDoorOpener_proof.

apply mk_cyber_capable.
intros; apply cyberCapability_proof.

apply mk_human_usable.
intros; apply humanUsability_proof.

apply mk_speed.
intros; apply speed_proof.
apply systemIsResponsive_proof.

apply mk_endurable.
intros; apply endurability_proof.

apply mk_maneuverable.
intros; apply maneuverability_proof.

apply mk_accurate.
intros; apply accuracy_proof.

apply mk_impact.
intros; apply impact_proof.

apply mk_scalable.
intros; apply scalability_proof.

apply mk_versatile.
intros; apply versability_proof.

apply mk_interoperable.
intros; apply interoperability_proof.
apply conj.
apply systemCanWorkWithOtherSystems_proof.
apply systemCanBeAccessedFromOtherSystems_proof.

apply mk_resource_utl.
apply mk_cost.
intros; apply cost_proof.

apply mk_duration.
intros; apply duration_proof.

apply mk_key_personnel.
intros; apply keyPersonnel_proof.

apply mk_other_scarce_resources.
intros; apply otherScareResources_proof.

apply mk_manufacturability.
intros; apply manufacturability_proof.

apply mk_sustainability.
intros; apply sustainability_proof.

apply mk_dependability.
apply mk_secure.
intros; apply security_proof.
apply conj.
apply systemIsDifficultToHack_proof.
apply systemDoesNotHarmOwners_proof.

apply mk_safe.
intros; apply safety_proof.

apply mk_reliability.
intros; apply reliability_proof.

apply mk_maintainability.
intros; apply maintainability_proof.

apply mk_availability.
intros; apply availability_proof.

apply mk_survivability.
intros; apply survivability_proof.

apply mk_robustness.
intros; apply robustness_proof.

apply isFlexible.
apply mk_modifiability.
intros; apply modifiability_proof.

apply mk_tailorability.
intros; apply tailorability_proof.

apply mk_adaptability.
intros. apply adaptability_proof.
apply systemMeetsSpecificAdaptabilityRequirement_proof.
simpl;right;left;auto.

apply isAffordable.
apply mk_mission_eff.
apply mk_physical_capable.
intros; apply physicalCapability_proof.
apply conj.
apply systemCanControlFurnaceOnOffSwitch_proof.
apply systemCanControlGarageDoorOpener_proof.

apply mk_cyber_capable.
intros; apply cyberCapability_proof.

apply mk_human_usable.
intros; apply humanUsability_proof.

apply mk_speed.
intros; apply speed_proof.
apply systemIsResponsive_proof.

apply mk_endurable.
intros; apply endurability_proof.

apply mk_maneuverable.
intros; apply maneuverability_proof.

apply mk_accurate.
intros; apply accuracy_proof.

apply mk_impact.
intros; apply impact_proof.

apply mk_scalable.
intros; apply scalability_proof.

apply mk_versatile.
intros; apply versability_proof.

apply mk_interoperable.
intros; apply interoperability_proof.
apply conj.
apply systemCanWorkWithOtherSystems_proof.
apply systemCanBeAccessedFromOtherSystems_proof.

apply mk_resource_utl.
apply mk_cost.
intros; apply cost_proof.

apply mk_duration.
intros; apply duration_proof.

apply mk_key_personnel.
intros; apply keyPersonnel_proof.

apply mk_other_scarce_resources.
intros; apply otherScareResources_proof.

apply mk_manufacturability.
intros; apply manufacturability_proof.

apply mk_sustainability.
intros; apply sustainability_proof.

apply isResilient.
apply mk_dependability.
apply mk_secure.
intros; apply security_proof.
apply conj.
apply systemIsDifficultToHack_proof.
apply systemDoesNotHarmOwners_proof.

apply mk_safe.
intros; apply safety_proof.

apply mk_reliability.
intros; apply reliability_proof.

apply mk_maintainability.
intros; apply maintainability_proof.

apply mk_availability.
intros; apply availability_proof.

apply mk_survivability.
intros; apply survivability_proof.

apply mk_robustness.
intros; apply robustness_proof.

apply isFlexible.
apply mk_modifiability.
intros; apply modifiability_proof.

apply mk_tailorability.
intros; apply tailorability_proof.

apply mk_adaptability.
intros. apply adaptability_proof.
apply systemMeetsSpecificAdaptabilityRequirement_proof.
simpl;right;left;auto.
Defined.
