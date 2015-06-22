Require Export Quality.
Require Export Value.
Require Export Example_Parnas.
Require Export BoehmTactics.

(**
[inputFormatChangeActionSpec] expresses a Ross-style changeability requirement
pertaining to system instances. We interpret this one as saying that 
when the [trigger] condition on a system instance state is true, then
the [agent] should be able to perform an operation that satisfies the
conditions formalized in the precondition/postcondition pair encoded 
in the function body. This function returns a proposition, a proof of
which shows that a given function does satisfy this condition. Here 
the condition requires that agent be [customer] and the KWIC system is 
using [input_format_one] and in the [maintenance] phase of its lifecycle, 
and if this is the case then a concrete operation must effect a transition
to a new state in which the input format is another, only one module was 
changed(that is, the number of modules remained the same), no more that 2
developers were involved, no more than 7 days were spent, at least 3 level
of satisfaction were increased, and at least 100 unit dollars were increased.
*)

Definition inputFormatChangeActionSpec (trigger: KWICAssertion) (agent: KWICStakeholders) (pre post: KWICSystemState): Prop  :=  
        agent = customer /\ inputFormatOne pre /\ inMaintenancePhase pre ->
        inputFormatAnother post /\ modules (value post) = modules (value pre) /\ 
                                   developers (value post) <= developers (value pre) + 2 /\
                                   developmentTime (value post) <= developmentTime (value pre) + 7 /\
                                   satisfaction (value pre) <= satisfaction (value post) + 3 /\
                                   dollars (value pre) < dollars (value post) + 100.

(**
This theorem and proof show that the [customerChangeImputFormat] function as 
defined here does satsify this specification.
*)
Require Import LibTactics.
Require Import Omega.

Theorem verifyChangeInputFormat: ActionSatisfiesActionSpec (inputFormatChangeActionSpec inputFormatOneState customer)  customerChangeImputFormat.
Proof.
unfold ActionSatisfiesActionSpec.
intros.
unfold inputFormatChangeActionSpec.
jauto_set.
unfold inputFormatAnother; auto.
simpl; omega. 
simpl; omega. 
simpl; omega. 
simpl; omega.
simpl; omega.
Qed.


(**
Now we write the [changebility] plug-in to the Boehm framework.
For any combination of context, phase, stakeholder, and state 
other than the combination of interest here, this function just
requires a trivial proof of [True]. In the one case of interest,
it requires a proof, such as [verifyChangeInputFormat], that
[ActionSatisfiesActionSpec (inputFormatChangeActionSpec 
inputFormatOneState customer)  customerChangeImputFormat].
*)

Definition kwic_changeability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop :=
  match c, p, s, st with
    | nominal, maintainance, customer, _ =>  ActionSatisfiesActionSpec (inputFormatChangeActionSpec inputFormatOneState customer)  customerChangeImputFormat
    | _, _, _, _ => True
  end.


Definition kwic_accuracy_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_physicalCapability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_cyberCapability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_humanUsability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_speed_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_endurability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_maneuverability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_impact_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_scalability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_versatility_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_interoperability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_missionEffectiveness_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.

Definition kwic_cost_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_duration_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_keyPersonnel_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_otherScarceResources_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_manufacturability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_sustainability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_efficiency_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.

Definition kwic_affordability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.

Definition kwic_security_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_safety_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_reliability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_maintainability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_availability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_survivability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_robustness_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_dependability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.

Definition kwic_modifiability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_tailorability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_adaptability_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.
Definition kwic_flexibility_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.

Definition kwic_resiliency_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.

Definition kwic_satisfactory_reqs (c: KWICContexts) (p: KWICPhases) (s: KWICStakeholders) (st: KWICSystemState): Prop := True.

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

Theorem kwic_changeability_certificate: @Changeable KWICSystemType.
Proof.
Prove_satisfaction kwic_changeability_reqs c p s
;simpl; exact verifyChangeInputFormat.
Qed.

Theorem kwic_accuracy_certificate: @Accurate KWICSystemType.
Proof.
Prove_satisfaction kwic_accuracy_reqs c p s.
Qed.

Theorem kwic_physicalCapability_certificate: @PhysicalCapable KWICSystemType.
Proof.
Prove_satisfaction kwic_physicalCapability_reqs c p s.     
Qed.

Theorem kwic_cyberCapability_certificate: @CyberCapable KWICSystemType.
Proof.
Prove_satisfaction kwic_cyberCapability_reqs c p s.    
Qed.

Theorem kwic_humanUsability_certificate: @HumanUsable KWICSystemType.
Proof.
Prove_satisfaction kwic_humanUsability_reqs c p s.  
Qed.

Theorem kwic_speed_certificate: @Speed KWICSystemType.
Proof.
Prove_satisfaction kwic_speed_reqs c p s. 
Qed.

Theorem kwic_endurability_certificate: @Endurable KWICSystemType.
Proof.
Prove_satisfaction kwic_endurability_reqs c p s.    
Qed.

Theorem kwic_maneuverability_certificate: @Maneuverable KWICSystemType.
Proof.
Prove_satisfaction kwic_maneuverability_reqs c p s.   
Qed.

Theorem kwic_impact_certificate: @Impactful KWICSystemType.
Proof.
Prove_satisfaction kwic_impact_reqs c p s. 
Qed.

Theorem kwic_scalability_certificate: @Scalable KWICSystemType.
Proof.
Prove_satisfaction kwic_scalability_reqs c p s.
Qed.

Theorem kwic_versatility_certificate: @Versatile KWICSystemType.
Proof.
Prove_satisfaction kwic_versatility_reqs c p s. 
Qed.

Theorem kwic_interoperability_certificate: @Interoperable KWICSystemType.
Proof.
Prove_satisfaction kwic_interoperability_reqs c p s.      
Qed.

Theorem kwic_cost_certificate: @Cost KWICSystemType.
Proof.
Prove_satisfaction kwic_cost_reqs c p s.  
Qed.

Theorem kwic_duration_certificate: @Duration KWICSystemType.
Proof.
Prove_satisfaction kwic_duration_reqs c p s.  
Qed.

Theorem kwic_keyPersonnel_certificate: @KeyPersonnel KWICSystemType.
Proof.
Prove_satisfaction kwic_keyPersonnel_reqs c p s.   
Qed.

Theorem kwic_otherScarceResources_certificate: @OtherScarceResources KWICSystemType.
Proof.
Prove_satisfaction kwic_otherScarceResources_reqs c p s.    
Qed.

Theorem kwic_manufacturability_certificate: @Manufacturable KWICSystemType.
Proof.
Prove_satisfaction kwic_manufacturability_reqs c p s.  
Qed.

Theorem kwic_sustainability_certificate: @Sustainable KWICSystemType.
Proof.
Prove_satisfaction kwic_sustainability_reqs c p s.    
Qed.

Theorem kwic_security_certificate: @Secure KWICSystemType.
Proof.
Prove_satisfaction kwic_security_reqs c p s.   
Qed.

Theorem kwic_safety_certificate: @Safe KWICSystemType.
Proof.
Prove_satisfaction kwic_safety_reqs c p s.  
Qed.

Theorem kwic_reliability_certificate: @Reliable KWICSystemType.
Proof.
Prove_satisfaction kwic_reliability_reqs c p s.  
Qed.

Theorem kwic_maintainability_certificate: @Maintainable KWICSystemType.
Proof.
Prove_satisfaction kwic_maintainability_reqs c p s.  
Qed.

Theorem kwic_availability_certificate: @Available KWICSystemType.
Proof.
Prove_satisfaction kwic_availability_reqs c p s.
Qed.

Theorem kwic_survivability_certificate: @Survivable KWICSystemType.
Proof.
Prove_satisfaction kwic_survivability_reqs c p s.  
Qed.

Theorem kwic_robustness_certificate: @Robust KWICSystemType.
Proof.
Prove_satisfaction kwic_robustness_reqs c p s.   
Qed.

Theorem kwic_modifiability_certificate: @Modifiable KWICSystemType.
Proof.
Prove_satisfaction kwic_modifiability_reqs c p s.   
Qed.

Theorem kwic_tailorability_certificate: @Tailorable KWICSystemType.
Proof.
Prove_satisfaction kwic_tailorability_reqs c p s.   
Qed.

Theorem kwic_adaptability_certificate: @Adaptable KWICSystemType.
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

Theorem kwic_missionEffectiveness_certificate: @MissionEffective KWICSystemType.
Proof.
auto.
Qed.

Theorem kwic_efficiency_certificate: @Efficient KWICSystemType.
Proof.
auto.
Qed.

Theorem kwic_flexibility_certificate: @Flexible KWICSystemType.
Proof.
auto.
Qed.

Theorem kwic_dependability_certificate: @Dependable KWICSystemType.
Proof.
auto.
Qed.

Theorem kwic_affordability_certificate: @Affordable KWICSystemType.
Proof.
auto.
Qed.

Theorem kwic_resiliency_certificate: @Resilient KWICSystemType.
Proof.
auto.
Qed.

Theorem kwic_satisfactory_certificate: @Satisfactory KWICSystemType.
Proof.
auto.
Qed.
































