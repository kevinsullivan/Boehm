Require Export Satisfactory.
Require Export Value.
Require Export Example_Parnas_Information_Hiding.
Require Export BoehmTactics.

(**
[corpusChangeActionSpec] expresses a Ross-style changeability requirement
pertaining to system instances. We interpret this one as saying that 
a system instance is changeable if 1) it is modular with respect to the
parameter that will be changed and 2)when the [trigger] condition on 
a system instance state is true, then the [agent] should be able to 
perform an operation that satisfies the conditions formalized in the 
precondition/postcondition pair encoded in the function body. 
This function returns a proposition, a proof of which shows that 
a given function does satisfy this condition. Here the condition requires 
that agent be [customer] and system is in its [corpusPre] state
and in the [maintanance] phase of its lifecycle, and if this is the case
then a concrete operation must effect a transition to a new state in
which the system is in its [corpusPost] state and no more than 1 module 
were changed due to the operation.
*)


Definition corpusChangeActionSpec (trigger: kwicAssertion) (agent: kwicStakeholders) (pre post: kwicSystemState): Prop  :=  
        isModular_wrt corpus pre /\ (trigger = corpusPreState /\ agent = customer /\ corpusPre pre /\ inMaintenancePhase pre ->
        corpusPost post /\ modulesChanged (value post) <= modulesChanged (value pre) + 1).

(**
This theorem and proof show that the [costomerChangeCorpus] function as 
defined here does satsify this specification.
*)

Theorem verifyChangeCorpus: ActionSatisfiesActionSpec (corpusChangeActionSpec corpusPre customer) costomerChangeCorpus.
Proof.
unfold ActionSatisfiesActionSpec.
intros.
unfold corpusChangeActionSpec.
intuition.
(*Prove isModular_wrt corpus s here.*)
Admitted.


(**
Now we write the [changebility] plug-in to the Boehm framework.
For any combination of context, phase, stakeholder, and state 
other than the combination of interest here, this function just
requires a trivial proof of [True]. In the one case of interest,
it requires a proof, such as [verifyChangeCorpus], that 
[ActionSatisfiesActionSpec (corpusChangeActionSpec 
corpusPre customer) costomerChangeCorpus.l].
*)
Definition kwic_changeability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop :=
  match c, p, s, st with
       | nominal, maintenance, customer, _ =>  ActionSatisfiesActionSpec (corpusChangeActionSpec corpusPre customer) costomerChangeCorpus
       | _, _, _, _ => True
  end.

Definition kwic_accuracy_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_physicalCapability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_cyberCapability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_humanUsability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_speed_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_endurability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_maneuverability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_impact_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_scalability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_versatility_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_interoperability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_missionEffectiveness_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.

Definition kwic_cost_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_duration_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_keyPersonnel_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_otherScarceResources_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_manufacturability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_sustainability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_efficiency_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.

Definition kwic_affordability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.

Definition kwic_security_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_safety_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_reliability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_maintainability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_availability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_survivability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_robustness_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_dependability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.

Definition kwic_modifiability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_tailorability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_adaptability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.
Definition kwic_flexibility_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.

Definition kwic_resiliency_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.

Definition kwic_satisfactory_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := True.

Hint Unfold kwic_changeability_reqs kwic_accuracy_reqs kwic_physicalCapability_reqs kwic_cyberCapability_reqs kwic_humanUsability_reqs
            kwic_speed_reqs kwic_endurability_reqs kwic_maneuverability_reqs kwic_impact_reqs kwic_scalability_reqs kwic_versatility_reqs
            kwic_interoperability_reqs kwic_missionEffectiveness_reqs kwic_cost_reqs kwic_duration_reqs kwic_keyPersonnel_reqs
            kwic_otherScarceResources_reqs kwic_manufacturability_reqs kwic_sustainability_reqs kwic_efficiency_reqs kwic_affordability_reqs
            kwic_security_reqs kwic_safety_reqs kwic_reliability_reqs kwic_maintainability_reqs kwic_availability_reqs kwic_survivability_reqs
            kwic_robustness_reqs kwic_dependability_reqs kwic_modifiability_reqs kwic_tailorability_reqs kwic_adaptability_reqs kwic_flexibility_reqs
            kwic_resiliency_reqs kwic_satisfactory_reqs.

(**
Proofs for satisfying ility requirements.
*)

Theorem kwic_changeability_certificate: @Changeable kwicSystemType.
Proof.
Prove_satisfaction kwic_changeability_reqs c p s
;simpl; exact verifyChangeCorpus.
Qed.

Theorem kwic_accuracy_certificate: @Accurate kwicSystemType.
Proof.
Prove_satisfaction kwic_accuracy_reqs c p s.
Qed.

Theorem kwic_physicalCapability_certificate: @PhysicalCapable kwicSystemType.
Proof.
Prove_satisfaction kwic_physicalCapability_reqs c p s.     
Qed.

Theorem kwic_cyberCapability_certificate: @CyberCapable kwicSystemType.
Proof.
Prove_satisfaction kwic_cyberCapability_reqs c p s.    
Qed.

Theorem kwic_humanUsability_certificate: @HumanUsable kwicSystemType.
Proof.
Prove_satisfaction kwic_humanUsability_reqs c p s.  
Qed.

Theorem kwic_speed_certificate: @Speed kwicSystemType.
Proof.
Prove_satisfaction kwic_speed_reqs c p s. 
Qed.

Theorem kwic_endurability_certificate: @Endurable kwicSystemType.
Proof.
Prove_satisfaction kwic_endurability_reqs c p s.    
Qed.

Theorem kwic_maneuverability_certificate: @Maneuverable kwicSystemType.
Proof.
Prove_satisfaction kwic_maneuverability_reqs c p s.   
Qed.

Theorem kwic_impact_certificate: @Impactful kwicSystemType.
Proof.
Prove_satisfaction kwic_impact_reqs c p s. 
Qed.

Theorem kwic_scalability_certificate: @Scalable kwicSystemType.
Proof.
Prove_satisfaction kwic_scalability_reqs c p s.
Qed.

Theorem kwic_versatility_certificate: @Versatile kwicSystemType.
Proof.
Prove_satisfaction kwic_versatility_reqs c p s. 
Qed.

Theorem kwic_interoperability_certificate: @Interoperable kwicSystemType.
Proof.
Prove_satisfaction kwic_interoperability_reqs c p s.      
Qed.

Theorem kwic_cost_certificate: @Cost kwicSystemType.
Proof.
Prove_satisfaction kwic_cost_reqs c p s.  
Qed.

Theorem kwic_duration_certificate: @Duration kwicSystemType.
Proof.
Prove_satisfaction kwic_duration_reqs c p s.  
Qed.

Theorem kwic_keyPersonnel_certificate: @KeyPersonnel kwicSystemType.
Proof.
Prove_satisfaction kwic_keyPersonnel_reqs c p s.   
Qed.

Theorem kwic_otherScarceResources_certificate: @OtherScarceResources kwicSystemType.
Proof.
Prove_satisfaction kwic_otherScarceResources_reqs c p s.    
Qed.

Theorem kwic_manufacturability_certificate: @Manufacturable kwicSystemType.
Proof.
Prove_satisfaction kwic_manufacturability_reqs c p s.  
Qed.

Theorem kwic_sustainability_certificate: @Sustainable kwicSystemType.
Proof.
Prove_satisfaction kwic_sustainability_reqs c p s.    
Qed.

Theorem kwic_security_certificate: @Secure kwicSystemType.
Proof.
Prove_satisfaction kwic_security_reqs c p s.   
Qed.

Theorem kwic_safety_certificate: @Safe kwicSystemType.
Proof.
Prove_satisfaction kwic_safety_reqs c p s.  
Qed.

Theorem kwic_reliability_certificate: @Reliable kwicSystemType.
Proof.
Prove_satisfaction kwic_reliability_reqs c p s.  
Qed.

Theorem kwic_maintainability_certificate: @Maintainable kwicSystemType.
Proof.
Prove_satisfaction kwic_maintainability_reqs c p s.  
Qed.

Theorem kwic_availability_certificate: @Available kwicSystemType.
Proof.
Prove_satisfaction kwic_availability_reqs c p s.
Qed.

Theorem kwic_survivability_certificate: @Survivable kwicSystemType.
Proof.
Prove_satisfaction kwic_survivability_reqs c p s.  
Qed.

Theorem kwic_robustness_certificate: @Robust kwicSystemType.
Proof.
Prove_satisfaction kwic_robustness_reqs c p s.   
Qed.

Theorem kwic_modifiability_certificate: @Modifiable kwicSystemType.
Proof.
Prove_satisfaction kwic_modifiability_reqs c p s.   
Qed.

Theorem kwic_tailorability_certificate: @Tailorable kwicSystemType.
Proof.
Prove_satisfaction kwic_tailorability_reqs c p s.   
Qed.

Theorem kwic_adaptability_certificate: @Adaptable kwicSystemType.
Proof.
Prove_satisfaction kwic_adaptability_reqs c p s.   
Qed.

Hint Resolve kwic_changeability_certificate kwic_physicalCapability_certificate kwic_cyberCapability_certificate kwic_humanUsability_certificate
             kwic_speed_certificate kwic_endurability_certificate kwic_maneuverability_certificate kwic_accuracy_certificate 
             kwic_impact_certificate kwic_scalability_certificate kwic_versatility_certificate kwic_interoperability_certificate
             kwic_cost_certificate kwic_duration_certificate kwic_keyPersonnel_certificate kwic_otherScarceResources_certificate
             kwic_manufacturability_certificate kwic_sustainability_certificate kwic_security_certificate kwic_safety_certificate 
             kwic_reliability_certificate kwic_maintainability_certificate kwic_availability_certificate kwic_survivability_certificate
             kwic_robustness_certificate kwic_modifiability_certificate kwic_tailorability_certificate kwic_adaptability_certificate.

Theorem kwic_missionEffectiveness_certificate: @MissionEffective kwicSystemType.
Proof.
auto.
Qed.

Theorem kwic_efficiency_certificate: @Efficient kwicSystemType.
Proof.
auto.
Qed.

Theorem kwic_flexibility_certificate: @Flexible kwicSystemType.
Proof.
auto.
Qed.

Theorem kwic_dependability_certificate: @Dependable kwicSystemType.
Proof.
auto.
Qed.

Theorem kwic_affordability_certificate: @Affordable kwicSystemType.
Proof.
auto.
Qed.

Theorem kwic_resiliency_certificate: @Resilient kwicSystemType.
Proof.
auto.
Qed.

Theorem kwic_satisfactory_certificate: @Satisfactory kwicSystemType.
Proof.
auto.
Qed.


































