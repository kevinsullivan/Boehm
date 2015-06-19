Require Export Quality.
Require Export Value.
Require Export Example_Car.

(**
[homeOilActionSpec] expresses a Ross-style changeability requirement
pertaining to system instances. We interpret this one as saying that 
when the [trigger] condition on a system instance state is true, then
the [agent] should be able to perform an operation that satisfies the
conditions formalized in the precondition/postcondition pair encoded 
in the function body. This function returns a proposition, a proof of
which shows that a given function does satisfy this condition. Here 
the condition requires that agent be [owner] and the car is at [home] 
and in the [ownership] phase of its lifecycle, and if this is the case
then a concrete operation must effect a transition to a new state in
which the oil is clean and no more than 60 minutes were spent on the
operation.  
*)

Definition homeOilActionSpec (trigger: CarAssertion) (agent: CarStakeholders) (pre post: CarSystemState): Prop  :=  
        agent = owner /\ atHome pre /\ inOwnershipPhase pre ->
        oilClean post /\ timeMinutes (value post) <= timeMinutes (value pre) + 60.

Hint Unfold homeOilActionSpec.

(**
This theorem and proof show that the [ownerChangeOil] function as 
defined here does satsify this specification.
*)

Require Import LibTactics.
Require Import Omega.

Theorem verifyChangeOil: ActionSatisfiesActionSpec (homeOilActionSpec oilDirtyState owner)  ownerChangeOil.
Proof.
unfold ActionSatisfiesActionSpec.
intros.
unfold homeOilActionSpec.
jauto_set.
unfold oilClean.
auto.
simpl; omega.
Qed.

(**
Now we write the [changebility] plug-in to the Boehm framework.
For any combination of context, phase, stakeholder, and state 
other than the combination of interest here, this function just
requires a trivial proof of [True]. In the one case of interest,
it requires a proof, such as [verifyChangeOil], that [VerifyAction 
(homeOilActionSpec oilDirtyState owner)  ownerChangeOil].
*)

Definition car_changeability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop :=
  match c, p, s, st with
    | home, ownership, owner, _ =>  ActionSatisfiesActionSpec (homeOilActionSpec oilDirty owner) ownerChangeOil
    | _, _, _, _ => True
  end.

Definition car_accuracy_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_physicalCapability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_cyberCapability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_humanUsability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_speed_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_endurability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_maneuverability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_impact_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_scalability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_versatility_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_interoperability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_missionEffectiveness_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.

Definition car_cost_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_duration_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_keyPersonnel_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_otherScarceResources_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_manufacturability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_sustainability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_efficiency_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.

Definition car_affordability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.

Definition car_security_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_safety_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_reliability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_maintainability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_availability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_survivability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_robustness_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_dependability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.

Definition car_modifiability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_tailorability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_adaptability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.
Definition car_flexibility_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.

Definition car_resiliency_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.

Definition car_satisfactory_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop := True.

Hint Unfold car_changeability_reqs car_accuracy_reqs car_physicalCapability_reqs car_cyberCapability_reqs car_humanUsability_reqs
            car_speed_reqs car_endurability_reqs car_maneuverability_reqs car_impact_reqs car_scalability_reqs car_versatility_reqs
            car_interoperability_reqs car_missionEffectiveness_reqs car_cost_reqs car_duration_reqs car_keyPersonnel_reqs
            car_otherScarceResources_reqs car_manufacturability_reqs car_sustainability_reqs car_efficiency_reqs car_affordability_reqs
            car_security_reqs car_safety_reqs car_reliability_reqs car_maintainability_reqs car_availability_reqs car_survivability_reqs
            car_robustness_reqs car_dependability_reqs car_modifiability_reqs car_tailorability_reqs car_adaptability_reqs car_flexibility_reqs
            car_resiliency_reqs car_satisfactory_reqs.

(**
Here's the proof. Clearly we need some proof automation here.
*)

Theorem car_changeability_certificate: @Changeable CarSystemType.
Proof.
constructor.
exists car_changeability_reqs.
intros.
destruct c, p, s; auto.
simpl. exact verifyChangeOil.
Qed.

Theorem car_accuracy_certificate: @Accurate CarSystemType.
Proof.
constructor.
exists car_accuracy_reqs.
intros.
destruct c, p, s; auto.  
Qed. 

Theorem car_physicalCapability_certificate: @PhysicalCapable CarSystemType.
Proof.
constructor.
exists car_physicalCapability_reqs.
intros.
destruct c, p, s; auto. 
Qed.

Theorem car_cyberCapability_certificate: @CyberCapable CarSystemType.
Proof.
constructor.
exists car_cyberCapability_reqs.
intros.
destruct c, p, s; auto.
Qed.

Theorem car_humanUsability_certificate: @HumanUsable CarSystemType.
Proof.
constructor.
exists car_humanUsability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_speed_certificate: @Speed CarSystemType.
Proof.
constructor.
exists car_speed_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_endurability_certificate: @Endurable CarSystemType.
Proof.
constructor.
exists car_endurability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_maneuverability_certificate: @Maneuverable CarSystemType.
Proof.
constructor.
exists car_maneuverability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_impact_certificate: @Impactful CarSystemType.
Proof.
constructor.
exists car_impact_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_scalability_certificate: @Scalable CarSystemType.
Proof.
constructor.
exists car_scalability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_versatility_certificate: @Versatile CarSystemType.
Proof.
constructor.
exists car_versatility_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_interoperability_certificate: @Interoperable CarSystemType.
Proof.
constructor.
exists car_interoperability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_missionEffectiveness_certificate: @MissionEffective CarSystemType.
Proof.
constructor.
apply car_physicalCapability_certificate.
apply car_cyberCapability_certificate.
apply car_humanUsability_certificate.
apply car_speed_certificate.
apply car_endurability_certificate.
apply car_maneuverability_certificate.
apply car_accuracy_certificate.
apply car_impact_certificate.
apply car_scalability_certificate.
apply car_versatility_certificate.
apply car_interoperability_certificate.
Qed.

Theorem car_cost_certificate: @Cost CarSystemType.
Proof.
constructor.
exists car_cost_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_duration_certificate: @Duration CarSystemType.
Proof.
constructor.
exists car_duration_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_keyPersonnel_certificate: @KeyPersonnel CarSystemType.
Proof.
constructor.
exists car_keyPersonnel_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_otherScarceResources_certificate: @OtherScarceResources CarSystemType.
Proof.
constructor.
exists car_otherScarceResources_reqs.
intros.
destruct c, p, s; auto.     
Qed.


Theorem car_manufacturability_certificate: @Manufacturable CarSystemType.
Proof.
constructor.
exists car_manufacturability_reqs.
intros.
destruct c, p, s; auto.     
Qed.


Theorem car_sustainability_certificate: @Sustainable CarSystemType.
Proof.
constructor.
exists car_sustainability_reqs.
intros.
destruct c, p, s; auto.     
Qed.


Theorem car_efficiency_certificate: @Efficient CarSystemType.
Proof.
constructor.
apply car_cost_certificate.
apply car_duration_certificate.
apply car_keyPersonnel_certificate.
apply car_otherScarceResources_certificate.
apply car_manufacturability_certificate.
apply car_sustainability_certificate.
Qed.


Theorem car_affordability_certificate: @Affordable CarSystemType.
Proof.
constructor.
apply car_missionEffectiveness_certificate.
apply car_efficiency_certificate.  
Qed.

Theorem car_security_certificate: @Secure CarSystemType.
Proof.
constructor.
exists car_security_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_safety_certificate: @Safe CarSystemType.
Proof.
constructor.
exists car_safety_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_reliability_certificate: @Reliable CarSystemType.
Proof.
constructor.
exists car_reliability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_maintainability_certificate: @Maintainable CarSystemType.
Proof.
constructor.
exists car_maintainability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_availability_certificate: @Available CarSystemType.
Proof.
constructor.
exists car_availability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_survivability_certificate: @Survivable CarSystemType.
Proof.
constructor.
exists car_survivability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_robustness_certificate: @Robust CarSystemType.
Proof.
constructor.
exists car_robustness_reqs.
intros.
destruct c, p, s; auto.     
Qed.


Theorem car_dependability_certificate: @Dependable CarSystemType.
Proof.
constructor.
apply car_security_certificate.
apply car_safety_certificate.
apply car_reliability_certificate.
apply car_maintainability_certificate.
apply car_availability_certificate.
apply car_survivability_certificate.
apply car_robustness_certificate.
Qed.

Theorem car_modifiability_certificate: @Modifiable CarSystemType.
Proof.
constructor.
exists car_modifiability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_tailorability_certificate: @Tailorable CarSystemType.
Proof.
constructor.
exists car_tailorability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_adaptability_certificate: @Adaptable CarSystemType.
Proof.
constructor.
exists car_adaptability_reqs.
intros.
destruct c, p, s; auto.     
Qed.

Theorem car_flexibility_certificate: @Flexible CarSystemType.
Proof.
constructor. 
apply car_modifiability_certificate.
apply car_tailorability_certificate.
apply car_adaptability_certificate.
Qed.

Theorem car_resiliency_certificate: @Resilient CarSystemType.
Proof.
constructor.
apply car_dependability_certificate.
apply car_flexibility_certificate.
apply car_changeability_certificate.
Qed.

Theorem car_satisfactory_certificate: @Satisfactory CarSystemType.
Proof.
constructor.
apply car_affordability_certificate.
apply car_resiliency_certificate.
Qed.