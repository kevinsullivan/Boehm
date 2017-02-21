import Qualities.Satisfactory
import SystemModel.Value
import Examples.Parnas.Information_Hiding

/-
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
-/

definition corpusChangeActionSpec (trigger: kwicAssertion) (agent: kwicStakeholders) (pre post: kwicSystemState): Prop  :=  
        --TODO
        --isModular_wrt corpus pre /\ 
        (trigger = corpusPreState /\ agent = kwicStakeholders.customer /\ corpusPre pre /\ inMaintenancePhase pre ->
        corpusPost post /\ post^.value^.modulesChanged <= pre^.value^.modulesChanged + 1)

theorem verifyChangeCorpus: ActionSatisfiesActionSpec (corpusChangeActionSpec corpusPre kwicStakeholders.customer) customerChangeCorpus :=
begin
    unfold ActionSatisfiesActionSpec,
    unfold corpusChangeActionSpec,
    intros,
    split,
    unfold corpusPost,
    reflexivity,
    unfold customerChangeCorpus,
    simp,
    apply nat.le_add_left
end

definition kwic_changeability_reqs : kwicContexts -> kwicPhases -> kwicStakeholders -> kwicSystemState -> Prop
| kwicContexts.nominal kwicPhases.maintenance kwicStakeholders.customer _ :=  ActionSatisfiesActionSpec (corpusChangeActionSpec corpusPre kwicStakeholders.customer) customerChangeCorpus
| _ _ _ _ := true

definition kwic_accuracy_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_physicalCapability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_cyberCapability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_humanUsability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_speed_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_endurability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_maneuverability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_impact_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_scalability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_versatility_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_interoperability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_missionEffectiveness_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true

definition kwic_cost_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_duration_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_keyPersonnel_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_otherScarceResources_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_manufacturability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_sustainability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_efficiency_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true

definition kwic_affordability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true

definition kwic_security_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_safety_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_reliability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_maintainability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_availability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_survivability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_robustness_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_dependability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true

definition kwic_modifiability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_tailorability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_adaptability_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true
definition kwic_flexibility_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true

definition kwic_resiliency_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true

definition kwic_satisfactory_reqs (c: kwicContexts) (p: kwicPhases) (s: kwicStakeholders) (st: kwicSystemState): Prop := true

theorem kwic_changeability_certificate: @Changeable kwicSystemType :=
begin
    constructor,
        fapply exists.intro,
        exact kwic_changeability_reqs,
        intros,
        destruct c,
                try {
                        repeat {
                                intros,
                                rewrite a,
                                apply true.intro
                        }
                },
                intros,
                rewrite a,
                destruct p,
                        try {
                                repeat {
                                        intros,
                                        rewrite a_1,
                                        apply true.intro
                                }
                        },
                        intros,
                        rewrite a_1,
                        destruct s,
                                try {
                                        repeat {
                                                intros,
                                                rewrite a_2,
                                                apply true.intro
                                        }
                                },
                                intros,
                                rewrite a_2,
                                apply verifyChangeCorpus,

                                try {
                                        repeat {
                                                intros,
                                                rewrite a_2,
                                                apply true.intro
                                        }
                                },
                        
                try {
                        repeat {
                                intros,
                                rewrite a,
                                apply true.intro
                        }
                },
end

theorem kwic_physicalCapability_certificate: @PhysicalCapable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_physicalCapability_reqs,
        intros,
        apply true.intro
end

theorem kwic_cyberCapability_certificate: @CyberCapable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_cyberCapability_reqs,
        intros,
        apply true.intro
end

theorem kwic_humanUsability_certificate: @HumanUsable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_humanUsability_reqs,
        intros,
        apply true.intro
end

theorem kwic_speed_certificate: @Speed kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_speed_reqs,
        intros,
        apply true.intro
end

theorem kwic_endurability_certificate: @Endurable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_endurability_reqs,
        intros,
        apply true.intro
end

theorem kwic_maneuverability_certificate: @Maneuverable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_maneuverability_reqs,
        intros,
        apply true.intro
end

theorem kwic_accuracy_certificate: @Accurate kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_accuracy_reqs,
        intros,
        apply true.intro
end

theorem kwic_impactfulness_certificate: @Impactful kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_impact_reqs,
        intros,
        apply true.intro
end

theorem kwic_scalability_certificate: @Scalable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_scalability_reqs,
        intros,
        apply true.intro
end

theorem kwic_versatility_certificate: @Versatile kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_versatility_reqs,
        intros,
        apply true.intro
end

theorem kwic_interoperability_certificate: @Interoperable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_interoperability_reqs,
        intros,
        apply true.intro
end

theorem kwic_missionEffectiveness_certificate: @MissionEffective kwicSystemType :=
begin
        constructor,
        apply kwic_physicalCapability_certificate,
        apply kwic_cyberCapability_certificate,
        apply kwic_humanUsability_certificate,
        apply kwic_speed_certificate,
        apply kwic_endurability_certificate,
        apply kwic_maneuverability_certificate,
        apply kwic_accuracy_certificate,
        apply kwic_impactfulness_certificate,
        apply kwic_scalability_certificate,
        apply kwic_versatility_certificate,
        apply kwic_interoperability_certificate
end

theorem kwic_cost_certificate: @Cost kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_cost_reqs,
        intros,
        apply true.intro
end

theorem kwic_duration_certificate: @Duration kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_duration_reqs,
        intros,
        apply true.intro
end

theorem kwic_keyPersonnel_certificate: @KeyPersonnel kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_keyPersonnel_reqs,
        intros,
        apply true.intro
end

theorem kwic_otherScarceResources_certificate: @OtherScarceResources kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_otherScarceResources_reqs,
        intros,
        apply true.intro
end

theorem kwic_manufacturability_certificate: @Manufacturable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_manufacturability_reqs,
        intros,
        apply true.intro
end

theorem kwic_sustainability_certificate: @Sustainable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_sustainability_reqs,
        intros,
        apply true.intro
end

theorem kwic_effiency_certificate: @Efficient kwicSystemType :=
begin
        constructor,
        apply kwic_cost_certificate,
        apply kwic_duration_certificate,
        apply kwic_keyPersonnel_certificate,
        apply kwic_otherScarceResources_certificate,
        apply kwic_manufacturability_certificate,
        apply kwic_sustainability_certificate
end

theorem kwic_affordability_certificate: @Affordable kwicSystemType :=
begin
        constructor,
        apply kwic_missionEffectiveness_certificate,
        apply kwic_effiency_certificate
end

theorem kwic_security_certificate: @Secure kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_security_reqs,
        intros,
        apply true.intro
end

theorem kwic_safety_certificate: @Safe kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_safety_reqs,
        intros,
        apply true.intro
end

theorem kwic_reliability_certificate: @Reliable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_reliability_reqs,
        intros,
        apply true.intro
end

theorem kwic_maintainability_certificate: @Maintainable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_maintainability_reqs,
        intros,
        apply true.intro
end

theorem kwic_avaibility_certificate: @Available kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_availability_reqs,
        intros,
        apply true.intro
end

theorem kwic_survivability_certificate: @Survivable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_survivability_reqs,
        intros,
        apply true.intro
end

theorem kwic_robustness_certificate: @Robust kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_robustness_reqs,
        intros,
        apply true.intro
end

theorem kwic_dependability_certificate: @Dependable kwicSystemType :=
begin
        split,
        apply kwic_security_certificate,
        apply kwic_safety_certificate,
        apply kwic_reliability_certificate,
        apply kwic_maintainability_certificate,
        apply kwic_avaibility_certificate,
        apply kwic_survivability_certificate,
        apply kwic_robustness_certificate
end

theorem kwic_modifiability_certificate: @Modifiable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_adaptability_reqs,
        intros,
        apply true.intro
end

theorem kwic_tailorability_certificate: @Tailorable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_tailorability_reqs,
        intros,
        apply true.intro
end

theorem kwic_adaptability_certificate: @Adaptable kwicSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact kwic_modifiability_reqs,
        intros,
        apply true.intro
end

theorem kwic_flexibility_certificate: @Flexible kwicSystemType :=
begin 
        constructor,
        apply kwic_modifiability_certificate,
        apply kwic_tailorability_certificate,
        apply kwic_adaptability_certificate
end

theorem kwic_resiliency_certificate: @Resilient kwicSystemType :=
begin
        constructor,
        apply kwic_dependability_certificate,
        apply kwic_flexibility_certificate,
        apply kwic_changeability_certificate
end

theorem kwic_satisfactory_certificate: @Satisfactory kwicSystemType :=
begin
        constructor,
        apply kwic_affordability_certificate,
        apply kwic_resiliency_certificate
end