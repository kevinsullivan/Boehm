import Qualities.Satisfactory
--import Value
import Examples.Car.Car_SystemModel
--import BoehmTactics

/-
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
-/

definition homeOilActionSpec (trigger: CarAssertion) (agent: CarStakeholders) (pre post: CarSystemState): Prop  :=  
        trigger = oilDirtyState /\ agent = CarStakeholders.owner /\ atHome pre /\ inOwnershipPhase pre ->
        oilClean post /\ post^.value^.timeMinutes <= pre^.value^.timeMinutes + 60


/-
This theorem and proof show that the [ownerChangeOil] function as 
defined here does satsify this specification.
-/

theorem verifyChangeOil: ActionSatisfiesActionSpec (homeOilActionSpec oilDirtyState CarStakeholders.owner)  ownerChangeOil :=
begin
        unfold ActionSatisfiesActionSpec,
        intros,
        unfold homeOilActionSpec,
        intros,
        clear a,
        split,
        unfold oilClean,
        reflexivity,
        apply nat.le_add_right
end

/-
Now we write the [changebility] plug-in to the Boehm framework.
For any combination of context, phase, stakeholder, and state 
other than the combination of interest here, this function just
requires a trivial proof of [True]. In the one case of interest,
it requires a proof, such as [verifyChangeOil], that [VerifyAction 
(homeOilActionSpec oilDirtyState owner)  ownerChangeOil].
-/

definition car_changeability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop
| CarContexts.home CarPhases.ownership CarStakeholders.owner _ := ActionSatisfiesActionSpec (homeOilActionSpec oilDirty CarStakeholders.owner) ownerChangeOil
| _ _ _ _ := true


/- An example -/
/-
def mycarvalue : CarValue :=
{timeMinutes:=0,moneyDollars:=0,gasolineGallons:=0,wearRate:=0}
def mycar : Car :=
{oilState:= {oilCleanliness:=OilCleanliness.oil_clean, oilFullness:=OilFullness.oil_full},tireState:=TireInflation.tire_full, location:=Location.l_home}
def mycarstate : CarSystemState :=
{context:=CarContexts.factory, phase:=CarPhases.manufacturing, artifact:=mycar, value:=mycarvalue}
-/

definition car_physicalCapability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_cyberCapability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_humanUsability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_speed_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_endurability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_maneuverability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_accuracy_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_impactfulness_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_scalability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_versatility_reqs  : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_interoperability_reqs  : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_cost_reqs  : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_duration_reqs  : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_keyPersonnel_reqs  : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_otherScarceResources_reqs  : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_manufacturability_reqs  : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_sustainability_reqs  : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_security_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_safety_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_reliability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_maintainability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_availability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_survivability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_robustness_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_modifiability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_tailorability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

definition car_adaptability_reqs : CarContexts -> CarPhases -> CarStakeholders -> CarSystemState -> Prop 
| _ _ _ _ := true

theorem car_changeability_certificate : @Changeable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_changeability_reqs,
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
                                apply verifyChangeOil,

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

theorem car_physicalCapability_certificate: @PhysicalCapable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_physicalCapability_reqs,
        intros,
        apply true.intro
end

theorem car_cyberCapability_certificate: @CyberCapable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_cyberCapability_reqs,
        intros,
        apply true.intro
end

theorem car_humanUsability_certificate: @HumanUsable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_humanUsability_reqs,
        intros,
        apply true.intro
end

theorem car_speed_certificate: @Speed CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_speed_reqs,
        intros,
        apply true.intro
end

theorem car_endurability_certificate: @Endurable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_endurability_reqs,
        intros,
        apply true.intro
end

theorem car_maneuverability_certificate: @Maneuverable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_maneuverability_reqs,
        intros,
        apply true.intro
end

theorem car_accuracy_certificate: @Accurate CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_accuracy_reqs,
        intros,
        apply true.intro
end

theorem car_impactfulness_certificate: @Impactful CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_impactfulness_reqs,
        intros,
        apply true.intro
end

theorem car_scalability_certificate: @Scalable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_scalability_reqs,
        intros,
        apply true.intro
end

theorem car_versatility_certificate: @Versatile CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_versatility_reqs,
        intros,
        apply true.intro
end

theorem car_interoperability_certificate: @Interoperable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_interoperability_reqs,
        intros,
        apply true.intro
end

theorem car_missionEffectiveness_certificate: @MissionEffective CarSystemType :=
begin
        constructor,
        apply car_physicalCapability_certificate,
        apply car_cyberCapability_certificate,
        apply car_humanUsability_certificate,
        apply car_speed_certificate,
        apply car_endurability_certificate,
        apply car_maneuverability_certificate,
        apply car_accuracy_certificate,
        apply car_impactfulness_certificate,
        apply car_scalability_certificate,
        apply car_versatility_certificate,
        apply car_interoperability_certificate
end

theorem car_cost_certificate: @Cost CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_cost_reqs,
        intros,
        apply true.intro
end

theorem car_duration_certificate: @Duration CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_duration_reqs,
        intros,
        apply true.intro
end

theorem car_keyPersonnel_certificate: @KeyPersonnel CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_keyPersonnel_reqs,
        intros,
        apply true.intro
end

theorem car_otherScarceResources_certificate: @OtherScarceResources CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_otherScarceResources_reqs,
        intros,
        apply true.intro
end

theorem car_manufacturability_certificate: @Manufacturable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_manufacturability_reqs,
        intros,
        apply true.intro
end

theorem car_sustainability_certificate: @Sustainable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_sustainability_reqs,
        intros,
        apply true.intro
end

theorem car_effiency_certificate: @Efficient CarSystemType :=
begin
        constructor,
        apply car_cost_certificate,
        apply car_duration_certificate,
        apply car_keyPersonnel_certificate,
        apply car_otherScarceResources_certificate,
        apply car_manufacturability_certificate,
        apply car_sustainability_certificate
end

theorem car_affordability_certificate: @Affordable CarSystemType :=
begin
        constructor,
        apply car_missionEffectiveness_certificate,
        apply car_effiency_certificate
end

theorem car_security_certificate: @Secure CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_security_reqs,
        intros,
        apply true.intro
end

theorem car_safety_certificate: @Safe CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_safety_reqs,
        intros,
        apply true.intro
end

theorem car_reliability_certificate: @Reliable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_reliability_reqs,
        intros,
        apply true.intro
end

theorem car_maintainability_certificate: @Maintainable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_maintainability_reqs,
        intros,
        apply true.intro
end

theorem car_avaibility_certificate: @Available CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_availability_reqs,
        intros,
        apply true.intro
end

theorem car_survivability_certificate: @Survivable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_survivability_reqs,
        intros,
        apply true.intro
end

theorem car_robustness_certificate: @Robust CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_robustness_reqs,
        intros,
        apply true.intro
end

theorem car_dependability_certificate: @Dependable CarSystemType :=
begin
        split,
        apply car_security_certificate,
        apply car_safety_certificate,
        apply car_reliability_certificate,
        apply car_maintainability_certificate,
        apply car_avaibility_certificate,
        apply car_survivability_certificate,
        apply car_robustness_certificate
end

theorem car_modifiability_certificate: @Modifiable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_adaptability_reqs,
        intros,
        apply true.intro
end

theorem car_tailorability_certificate: @Tailorable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_tailorability_reqs,
        intros,
        apply true.intro
end

theorem car_adaptability_certificate: @Adaptable CarSystemType :=
begin
        constructor,
        fapply exists.intro,
        exact car_modifiability_reqs,
        intros,
        apply true.intro
end

theorem car_flexibility_certificate: @Flexible CarSystemType :=
begin 
        constructor,
        apply car_modifiability_certificate,
        apply car_tailorability_certificate,
        apply car_adaptability_certificate
end

theorem car_resiliency_certificate: @Resilient CarSystemType :=
begin
        constructor,
        apply car_dependability_certificate,
        apply car_flexibility_certificate,
        apply car_changeability_certificate
end

theorem car_satisfactory_certificate: @Satisfactory CarSystemType :=
begin
        constructor,
        apply car_affordability_certificate,
        apply car_resiliency_certificate
end