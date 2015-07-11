Require Export Quality.
Require Export Value.
Require Export Example_Car.
Require Export BoehmTactics.

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

(**
This theorem and proof show that the [ownerChangeOil] function as 
defined here does satsify this specification.
*)

Require Import Omega.

Theorem verifyChangeOil: ActionSatisfiesActionSpec (homeOilActionSpec oilDirtyState owner)  ownerChangeOil.
Proof.
  unfold ActionSatisfiesActionSpec.
  intros.
  simpl.
  unfold homeOilActionSpec.
  split.
  inversion H. clear H0 H.
  inversion H1.
  unfold oilClean.
  reflexivity.
  simpl. omega.
Qed.

(**
Now we write the [changebility] plug-in to the Boehm framework.
For any combination of context, phase, stakeholder, and state 
other than the combination of interest here, this function just
requires a trivial proof of [True]. In the one case of interest,
it requires a proof, such as [verifyChangeOil], that [VerifyAction 
(homeOilActionSpec oilDirtyState owner)  ownerChangeOil].
*)

Theorem car_modularity_certificate : modular car_dep.
  Proof.
    unfold modular.
    split.
    unfold no_circular_satisfaction. intuition.
    split.
    unfold satisfy_and_encapsulate_coupled. intuition.
    unfold hides_volatility. intros.
    destruct H.
    inversion H.
    unfold Uses in H; simpl in H.
    destruct a, b; inversion H.
    exists engine_module. simpl. auto.
    exists engine_module. simpl. auto.
  Qed.

Definition car_changeability_reqs (c: CarContexts) (p: CarPhases) (s: CarStakeholders) (st: CarSystemState): Prop :=
  isModular st /\ (match c, p, s, st with
       | home, ownership, owner, _ =>  ActionSatisfiesActionSpec (homeOilActionSpec oilDirty owner) ownerChangeOil
       | _, _, _, _ => True
     end).

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
Proofs for satisfying ility requirements.
 *)

Theorem car_changeability_certificate: @Changeable CarSystemType.
Proof.
  constructor. exists car_changeability_reqs. intros. constructor.
  unfold isModular. destruct (car_design (artifact st)). rewrite e. simpl. exact car_modularity_certificate. 
  destruct c, p, st; auto.
  simpl. destruct s; auto. exact verifyChangeOil.
Qed.

Theorem car_accuracy_certificate: @Accurate CarSystemType.
Proof.
  Prove_satisfaction car_accuracy_reqs c p s. 
Qed. 

Theorem car_physicalCapability_certificate: @PhysicalCapable CarSystemType.
Proof.
  Prove_satisfaction car_physicalCapability_reqs c p s.
Qed.

Theorem car_cyberCapability_certificate: @CyberCapable CarSystemType.
Proof.
  Prove_satisfaction car_cyberCapability_reqs c p s.
Qed.

Theorem car_humanUsability_certificate: @HumanUsable CarSystemType.
Proof.
  Prove_satisfaction car_humanUsability_reqs c p s.   
Qed.

Theorem car_speed_certificate: @Speed CarSystemType.
Proof.
  Prove_satisfaction car_speed_reqs c p s.     
Qed.

Theorem car_endurability_certificate: @Endurable CarSystemType.
Proof.
  Prove_satisfaction car_endurability_reqs c p s.  
Qed.

Theorem car_maneuverability_certificate: @Maneuverable CarSystemType.
Proof.
  Prove_satisfaction car_maneuverability_reqs c p s.    
Qed.

Theorem car_impact_certificate: @Impactful CarSystemType.
Proof.
  Prove_satisfaction car_impact_reqs c p s.    
Qed.

Theorem car_scalability_certificate: @Scalable CarSystemType.
Proof.
  Prove_satisfaction car_scalability_reqs c p s.    
Qed.

Theorem car_versatility_certificate: @Versatile CarSystemType.
Proof.
  Prove_satisfaction car_versatility_reqs c p s.    
Qed.

Theorem car_interoperability_certificate: @Interoperable CarSystemType.
Proof.
  Prove_satisfaction car_interoperability_reqs c p s.     
Qed.

Theorem car_cost_certificate: @Cost CarSystemType.
Proof.
  Prove_satisfaction car_cost_reqs c p s.   
Qed.

Theorem car_duration_certificate: @Duration CarSystemType.
Proof.
  Prove_satisfaction car_duration_reqs c p s.     
Qed.

Theorem car_keyPersonnel_certificate: @KeyPersonnel CarSystemType.
Proof.
  Prove_satisfaction car_keyPersonnel_reqs c p s.   
Qed.

Theorem car_otherScarceResources_certificate: @OtherScarceResources CarSystemType.
Proof.
  Prove_satisfaction car_otherScarceResources_reqs c p s.     
Qed.

Theorem car_manufacturability_certificate: @Manufacturable CarSystemType.
Proof.
  Prove_satisfaction car_manufacturability_reqs c p s.
Qed.

Theorem car_sustainability_certificate: @Sustainable CarSystemType.
Proof.
  Prove_satisfaction car_sustainability_reqs c p s.    
Qed.

Theorem car_security_certificate: @Secure CarSystemType.
Proof.
  Prove_satisfaction car_security_reqs c p s.
Qed.

Theorem car_safety_certificate: @Safe CarSystemType.
Proof.
  Prove_satisfaction car_safety_reqs c p s.    
Qed.

Theorem car_reliability_certificate: @Reliable CarSystemType.
Proof.
  Prove_satisfaction car_reliability_reqs c p s.   
Qed.

Theorem car_maintainability_certificate: @Maintainable CarSystemType.
Proof.
  Prove_satisfaction car_maintainability_reqs c p s.    
Qed.

Theorem car_availability_certificate: @Available CarSystemType.
Proof.
  Prove_satisfaction car_availability_reqs c p s.   
Qed.

Theorem car_survivability_certificate: @Survivable CarSystemType.
Proof.
  Prove_satisfaction car_survivability_reqs c p s.    
Qed.

Theorem car_robustness_certificate: @Robust CarSystemType.
Proof.
  Prove_satisfaction car_robustness_reqs c p s.  
Qed.

Theorem car_modifiability_certificate: @Modifiable CarSystemType.
Proof.
  Prove_satisfaction car_modifiability_reqs c p s.    
Qed.

Theorem car_tailorability_certificate: @Tailorable CarSystemType.
Proof.
  Prove_satisfaction car_tailorability_reqs c p s.    
Qed.

Theorem car_adaptability_certificate: @Adaptable CarSystemType.
Proof.
  Prove_satisfaction car_adaptability_reqs c p s.  
Qed.

Hint Resolve car_changeability_certificate car_physicalCapability_certificate car_cyberCapability_certificate car_humanUsability_certificate
     car_speed_certificate car_endurability_certificate car_maneuverability_certificate car_accuracy_certificate 
     car_impact_certificate car_scalability_certificate car_versatility_certificate car_interoperability_certificate
     car_cost_certificate car_duration_certificate car_keyPersonnel_certificate car_otherScarceResources_certificate
     car_manufacturability_certificate car_sustainability_certificate car_security_certificate car_safety_certificate 
     car_reliability_certificate car_maintainability_certificate car_availability_certificate car_survivability_certificate
     car_robustness_certificate car_modifiability_certificate car_tailorability_certificate car_adaptability_certificate.



Theorem car_missionEffectiveness_certificate: @MissionEffective CarSystemType.
Proof.
  auto.
Qed.

Theorem car_efficiency_certificate: @Efficient CarSystemType.
Proof.
  auto.
Qed.

Theorem car_flexibility_certificate: @Flexible CarSystemType.
Proof.
  auto.
Qed.

Theorem car_dependability_certificate: @Dependable CarSystemType.
Proof.
  auto.
Qed.

Theorem car_affordability_certificate: @Affordable CarSystemType.
Proof.
  auto.  
Qed.

Theorem car_resiliency_certificate: @Resilient CarSystemType.
Proof.
  auto.
Qed.

Theorem car_satisfactory_certificate: @Satisfactory CarSystemType.
Proof.
  auto.
Qed.

