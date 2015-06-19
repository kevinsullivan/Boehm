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
Hint Unfold inputFormatChangeActionSpec.
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
unfold inputFormatAnother.
auto. auto. 
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
Here's the proof. Clearly we need some proof automation here.
*)

Theorem kwic_changeability_certificate: @Changeable KWICSystemType.
Proof.
constructor.
exists kwic_changeability_reqs.
intros.
destruct c, p, s.
auto.
simpl; exact verifyChangeInputFormat.
auto.
simpl; exact verifyChangeInputFormat.
auto;
simpl; exact verifyChangeInputFormat.
auto.
simpl; exact verifyChangeInputFormat.
auto.
simpl; exact verifyChangeInputFormat.
auto.
simpl; exact verifyChangeInputFormat.
auto.
simpl; exact verifyChangeInputFormat.
Qed.

Theorem kwic_accuracy_certificate: @Accurate KWICSystemType.
Proof.
constructor.
exists kwic_accuracy_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto.  
auto. auto. auto. auto. auto. auto.
Qed.

Theorem kwic_physicalCapability_certificate: @PhysicalCapable KWICSystemType.
Proof.
constructor.
exists kwic_physicalCapability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.     
Qed.

Theorem kwic_cyberCapability_certificate: @CyberCapable KWICSystemType.
Proof.
constructor.
exists kwic_cyberCapability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.     
Qed.

Theorem kwic_humanUsability_certificate: @HumanUsable KWICSystemType.
Proof.
constructor.
exists kwic_humanUsability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_speed_certificate: @Speed KWICSystemType.
Proof.
constructor.
exists kwic_speed_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_endurability_certificate: @Endurable KWICSystemType.
Proof.
constructor.
exists kwic_endurability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_maneuverability_certificate: @Maneuverable KWICSystemType.
Proof.
constructor.
exists kwic_maneuverability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_impact_certificate: @Impactful KWICSystemType.
Proof.
constructor.
exists kwic_impact_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_scalability_certificate: @Scalable KWICSystemType.
Proof.
constructor.
exists kwic_scalability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_versatility_certificate: @Versatile KWICSystemType.
Proof.
constructor.
exists kwic_versatility_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_interoperability_certificate: @Interoperable KWICSystemType.
Proof.
constructor.
exists kwic_interoperability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_missionEffectiveness_certificate: @MissionEffective KWICSystemType.
Proof.
constructor.
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
Proof.
constructor.
exists kwic_cost_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_duration_certificate: @Duration KWICSystemType.
Proof.
constructor.
exists kwic_duration_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_keyPersonnel_certificate: @KeyPersonnel KWICSystemType.
Proof.
constructor.
exists kwic_keyPersonnel_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_otherScarceResources_certificate: @OtherScarceResources KWICSystemType.
Proof.
constructor.
exists kwic_otherScarceResources_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.


Theorem kwic_manufacturability_certificate: @Manufacturable KWICSystemType.
Proof.
constructor.
exists kwic_manufacturability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.


Theorem kwic_sustainability_certificate: @Sustainable KWICSystemType.
Proof.
constructor.
exists kwic_sustainability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.


Theorem kwic_efficiency_certificate: @Efficient KWICSystemType.
Proof.
constructor.
apply kwic_cost_certificate.
apply kwic_duration_certificate.
apply kwic_keyPersonnel_certificate.
apply kwic_otherScarceResources_certificate.
apply kwic_manufacturability_certificate.
apply kwic_sustainability_certificate.
Qed.


Theorem kwic_affordability_certificate: @Affordable KWICSystemType.
Proof.
constructor.
apply kwic_missionEffectiveness_certificate.
apply kwic_efficiency_certificate.  
Qed.

Theorem kwic_security_certificate: @Secure KWICSystemType.
Proof.
constructor.
exists kwic_security_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_safety_certificate: @Safe KWICSystemType.
Proof.
constructor.
exists kwic_safety_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_reliability_certificate: @Reliable KWICSystemType.
Proof.
constructor.
exists kwic_reliability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_maintainability_certificate: @Maintainable KWICSystemType.
Proof.
constructor.
exists kwic_maintainability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_availability_certificate: @Available KWICSystemType.
Proof.
constructor.
exists kwic_availability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_survivability_certificate: @Survivable KWICSystemType.
Proof.
constructor.
exists kwic_survivability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_robustness_certificate: @Robust KWICSystemType.
Proof.
constructor.
exists kwic_robustness_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.


Theorem kwic_dependability_certificate: @Dependable KWICSystemType.
Proof.
constructor.
apply kwic_security_certificate.
apply kwic_safety_certificate.
apply kwic_reliability_certificate.
apply kwic_maintainability_certificate.
apply kwic_availability_certificate.
apply kwic_survivability_certificate.
apply kwic_robustness_certificate.
Qed.

Theorem kwic_modifiability_certificate: @Modifiable KWICSystemType.
Proof.
constructor.
exists kwic_modifiability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_tailorability_certificate: @Tailorable KWICSystemType.
Proof.
constructor.
exists kwic_tailorability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_adaptability_certificate: @Adaptable KWICSystemType.
Proof.
constructor.
exists kwic_adaptability_reqs.
intros.
destruct c, p, s.
auto. auto. auto. auto. auto. auto. 
auto. auto. auto. auto. auto. auto.   
Qed.

Theorem kwic_flexibility_certificate: @Flexible KWICSystemType.
Proof.
constructor.
apply kwic_modifiability_certificate.
apply kwic_tailorability_certificate.
apply kwic_adaptability_certificate.
Qed.

Theorem kwic_resiliency_certificate: @Resilient KWICSystemType.
Proof.
constructor.
apply kwic_dependability_certificate.
apply kwic_flexibility_certificate.
apply kwic_changeability_certificate.
Qed.

Theorem kwic_satisfactory_certificate: @Satisfactory KWICSystemType.
Proof.
constructor.
apply kwic_affordability_certificate.
apply kwic_resiliency_certificate.
Qed.
































