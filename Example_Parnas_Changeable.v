Require Export Quality.
Require Export Value.
Require Export Example_Parnas.

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

Theorem verifyChangeInputFormat: ActionSatisfiesActionSpec (inputFormatChangeActionSpec inputFormatOneState customer)  customerChangeImputFormat.
(* auto works here *)
unfold ActionSatisfiesActionSpec.
intros.
unfold inputFormatChangeActionSpec.
intros.
split.
unfold inputFormatAnother.
simpl.
reflexivity.
simpl.
split.
reflexivity.
split.
Require Import Omega.
omega.
split.
omega.
split.
omega.
omega.
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


(**
Here's the proof. Clearly we need some proof automation here.
*)

Theorem kwic_changeability_certificate: @Changeable KWICSystemType.
apply satisfiesChangeabilityRequirements.
exists kwic_changeability_reqs.
intros.
destruct c, p, s.
simpl. exact I.
simpl. exact verifyChangeInputFormat.
simpl. exact I.
simpl. exact verifyChangeInputFormat.
simpl. exact I.
simpl. exact verifyChangeInputFormat.
simpl. exact I.
simpl. exact verifyChangeInputFormat.
simpl. exact I.
simpl. exact verifyChangeInputFormat.
simpl. exact I.
simpl. exact verifyChangeInputFormat.
Qed.

Theorem kwic_accuracy_certificate: @Accurate KWICSystemType.
apply satisfiesAccuracyRequirements.
exists kwic_accuracy_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_physicalCapability_certificate: @PhysicalCapable KWICSystemType.
apply satisfiesPhysicalCapabilityRequirements.
exists kwic_physicalCapability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.     
Qed.

Theorem kwic_cyberCapability_certificate: @CyberCapable KWICSystemType.
apply satisfiesCyberCapabilityRequirements.
exists kwic_cyberCapability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.     
Qed.

Theorem kwic_humanUsability_certificate: @HumanUsable KWICSystemType.
apply satisfiesHumanUsabilityRequirements.
exists kwic_humanUsability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_speed_certificate: @Speed KWICSystemType.
apply satisfiesSpeedRequirements.
exists kwic_speed_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_endurability_certificate: @Endurable KWICSystemType.
apply satisfiesEndurabilityRequirements.
exists kwic_endurability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_maneuverability_certificate: @Maneuverable KWICSystemType.
apply satisfiesManeuverabilityRequirements.
exists kwic_maneuverability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_impact_certificate: @Impactful KWICSystemType.
apply satisfiesImpactRequirements.
exists kwic_impact_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_scalability_certificate: @Scalable KWICSystemType.
apply satisfiesScalabilityRequirements.
exists kwic_scalability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_versatility_certificate: @Versatile KWICSystemType.
apply satisfiesVersatilityRequirements.
exists kwic_versatility_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_interoperability_certificate: @Interoperable KWICSystemType.
apply satisfiesInteroperabilityRequirements.
exists kwic_interoperability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_missionEffectiveness_certificate: @MissionEffective KWICSystemType.
apply satisfiesMissionEffectivenessPrerequisites.
apply kwic_physicalCapability_certificate.
apply kwic_cyberCapability_certificate.
apply kwic_humanUsability_certificate.
apply kwic_speed_certificate.
apply kwic_endurability_certificate.
apply kwic_maneuverability_certificate.
apply kwic_accuracy_certificate.
apply kwic_impact_certificate.
apply kwic_scalability_certificate.
apply kwic_versatility_certificate.
apply kwic_interoperability_certificate.
Qed.

Theorem kwic_cost_certificate: @Cost KWICSystemType.
apply satisfiesCostRequirements.
exists kwic_cost_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_duration_certificate: @Duration KWICSystemType.
apply satisfiesDurationRequirements.
exists kwic_duration_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_keyPersonnel_certificate: @KeyPersonnel KWICSystemType.
apply satisfiesKeyPersonnelRequirements.
exists kwic_keyPersonnel_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_otherScarceResources_certificate: @OtherScarceResources KWICSystemType.
apply satisfiesOtherResourcesRequirements.
exists kwic_otherScarceResources_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.


Theorem kwic_manufacturability_certificate: @Manufacturable KWICSystemType.
apply satisfiesManufacturabilityRequirements.
exists kwic_manufacturability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.


Theorem kwic_sustainability_certificate: @Sustainable KWICSystemType.
apply satisfiesSustainabilityRequirements.
exists kwic_sustainability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.


Theorem kwic_efficiency_certificate: @Efficient KWICSystemType.
apply satisfiesEfficiencyPrerequisites.
apply kwic_cost_certificate.
apply kwic_duration_certificate.
apply kwic_keyPersonnel_certificate.
apply kwic_otherScarceResources_certificate.
apply kwic_manufacturability_certificate.
apply kwic_sustainability_certificate.
Qed.


Theorem kwic_affordability_certificate: @Affordable KWICSystemType.
apply satisfiesAffordabilityPrerequisites.
apply kwic_missionEffectiveness_certificate.
apply kwic_efficiency_certificate.  
Qed.

Theorem kwic_security_certificate: @Secure KWICSystemType.
apply satisfiesSecurityRequirements.
exists kwic_security_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_safety_certificate: @Safe KWICSystemType.
apply satisfiesSafetyRequirements.
exists kwic_safety_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_reliability_certificate: @Reliable KWICSystemType.
apply satisfiesReliabilityRequirements.
exists kwic_reliability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_maintainability_certificate: @Maintainable KWICSystemType.
apply satisfiesMaintainabilityRequirements.
exists kwic_maintainability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_availability_certificate: @Available KWICSystemType.
apply satisfiesAvailabilityRequirements.
exists kwic_availability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_survivability_certificate: @Survivable KWICSystemType.
apply satisfiesSurvivabilityRequirements.
exists kwic_survivability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_robustness_certificate: @Robust KWICSystemType.
apply satisfiesRobustnessRequirements.
exists kwic_robustness_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.


Theorem kwic_dependability_certificate: @Dependable KWICSystemType.
apply satisfiesDependabilityPrerequisites.
apply kwic_security_certificate.
apply kwic_safety_certificate.
apply kwic_reliability_certificate.
apply kwic_maintainability_certificate.
apply kwic_availability_certificate.
apply kwic_survivability_certificate.
apply kwic_robustness_certificate.
Qed.

Theorem kwic_modifiability_certificate: @Modifiable KWICSystemType.
apply satisfiesModifiabilityRequirements.
exists kwic_modifiability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_tailorability_certificate: @Tailorable KWICSystemType.
apply satisfiesTailorabilityRequirements.
exists kwic_tailorability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_adaptability_certificate: @Adaptable KWICSystemType.
apply satisfiesAdaptabilityRequirements.
exists kwic_adaptability_reqs.
intros.
destruct c, p, s.
exact I. exact I. exact I. exact I. exact I. exact I. 
exact I. exact I. exact I. exact I. exact I. exact I.   
Qed.

Theorem kwic_flexibility_certificate: @Flexible KWICSystemType.
apply satisfiesFlexibilityPrerequisites. 
apply kwic_modifiability_certificate.
apply kwic_tailorability_certificate.
apply kwic_adaptability_certificate.
Qed.

Theorem kwic_resiliency_certificate: @Resilient KWICSystemType.
apply satisfiesResiliencyPrerequisites.
apply kwic_dependability_certificate.
apply kwic_flexibility_certificate.
apply kwic_changeability_certificate.
Qed.

Theorem kwic_satisfactory_certificate: @Satisfactory KWICSystemType.
apply meetsSatisfactoryRequirementss.
apply kwic_affordability_certificate.
apply kwic_resiliency_certificate.
Qed.
































