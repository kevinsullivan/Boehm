(** * System Quality General Theory *)

(*
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross
March, 2015
*)
Add Rec LoadPath "./ContributeQA".
Add Rec LoadPath "./Changeability".

Require Export MissionEffective.
Require Export ResourceUtilization.
Require Export Dependable.
Require Export Flexible.
Require Export Changeable.
Require Export Affordable.
Require Export Resilient.

Class Satisfactory (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set):= {
      sys: System

    ; physicalCapability : System -> Stakeholder -> Context -> Phase -> Prop
    ; cyberCapability : System -> Stakeholder -> Context -> Phase -> Prop
    ; humanUsability : System -> Stakeholder -> Context -> Phase -> Prop
    ; speed : System -> Stakeholder -> Context -> Phase -> Prop
    ; endurability : System -> Stakeholder -> Context -> Phase -> Prop
    ; maneuverability : System -> Stakeholder -> Context -> Phase -> Prop
    ; accuracy : System -> Stakeholder -> Context -> Phase -> Prop
    ; impact : System -> Stakeholder -> Context -> Phase -> Prop
    ; scalability : System -> Stakeholder -> Context -> Phase -> Prop
    ; versability : System -> Stakeholder -> Context -> Phase -> Prop
    ; interoperability : System -> Stakeholder -> Context -> Phase -> Prop

    ; cost : System -> Stakeholder -> Context -> Phase -> Prop
    ; duration : System -> Stakeholder -> Context -> Phase -> Prop
    ; keyPersonnel : System -> Stakeholder -> Context -> Phase -> Prop
    ; otherScareResources : System -> Stakeholder -> Context -> Phase -> Prop
    ; manufacturability : System -> Stakeholder -> Context -> Phase -> Prop
    ; sustainability : System -> Stakeholder -> Context -> Phase -> Prop

    ; security : System -> Stakeholder -> Context -> Phase -> Prop
    ; safety : System -> Stakeholder -> Context -> Phase -> Prop
    ; reliability : System -> Stakeholder -> Context -> Phase -> Prop
    ; maintainability : System -> Stakeholder -> Context -> Phase -> Prop
    ; availability : System -> Stakeholder -> Context -> Phase -> Prop
    ; survivability : System -> Stakeholder -> Context -> Phase -> Prop
    ; robustness : System -> Stakeholder -> Context -> Phase -> Prop

    ; modifiability : System -> Stakeholder -> Context -> Phase -> Prop
    ; tailorability : System -> Stakeholder -> Context -> Phase -> Prop
    ; adaptability : System -> Stakeholder -> Context -> Phase -> Prop

    ; valueRobustness: System -> Stakeholder -> Context -> Phase -> Prop
    ; valueSurvivability: System -> Stakeholder -> Context -> Phase -> Prop 
    ; ross_robustness: System -> Stakeholder -> Context -> Phase -> Prop 
    ; classicalPassiveRobustness: System -> Stakeholder -> Context -> Phase -> Prop 
    ; ross_survivability: System -> Stakeholder -> Context -> Phase -> Prop 
    ; evolvability: System -> Stakeholder -> Context -> Phase -> Prop 
    ; ross_adaptability: System -> Stakeholder -> Context -> Phase -> Prop 
    ; ross_flexibility: System -> Stakeholder -> Context -> Phase -> Prop 
    ; ross_scalability: System -> Stakeholder -> Context -> Phase -> Prop 
    ; ross_modifiability: System -> Stakeholder -> Context -> Phase -> Prop 
    ; extensibility: System -> Stakeholder -> Context -> Phase -> Prop 
    ; agility: System -> Stakeholder -> Context -> Phase -> Prop 
    ; reactivity: System -> Stakeholder -> Context -> Phase -> Prop 
    ; formReconfigurability: System -> Stakeholder -> Context -> Phase -> Prop 
    ; operationalReconfigurability: System -> Stakeholder -> Context -> Phase -> Prop 
    ; functionalVersatility: System -> Stakeholder -> Context -> Phase -> Prop 
    ; operationalVersatility: System -> Stakeholder -> Context -> Phase -> Prop 
    ; exchangeability: System -> Stakeholder -> Context -> Phase -> Prop 

    ; mission_effective: MissionEffective System Stakeholder Context Phase sys physicalCapability cyberCapability humanUsability speed
              endurability maneuverability accuracy impact scalability versability interoperability
    ; resource_utilization: ResourceUtilization System Stakeholder Context Phase sys cost duration keyPersonnel otherScareResources manufacturability sustainability
    ; dependable: Dependable System Stakeholder Context Phase sys security safety reliability maintainability availability survivability robustness
    ; flexible: Flexible System Stakeholder Context Phase sys modifiability tailorability adaptability
    ; changeable: Changeable System Stakeholder Context Phase sys valueRobustness valueSurvivability ross_robustness
               classicalPassiveRobustness ross_survivability evolvability ross_adaptability ross_flexibility
               ross_scalability ross_modifiability extensibility agility reactivity formReconfigurability
               operationalReconfigurability functionalVersatility operationalVersatility exchangeability

    (* affordable is a composite property of "MissionEffective" and "ResourceUtilization"*)
    ; affordable: Affordable System Stakeholder Context Phase sys
                             physicalCapability cyberCapability humanUsability speed
                             endurability maneuverability accuracy impact scalability versability interoperability
                             cost duration keyPersonnel otherScareResources manufacturability sustainability
    (* Resilient is a composite property of "Dependable", "Flexible" and "Changeable" *)
    ; resilient: Resilient System Stakeholder Context Phase sys
                           security safety reliability maintainability availability survivability robustness
                           modifiability tailorability adaptability valueRobustness valueSurvivability ross_robustness
                           classicalPassiveRobustness ross_survivability evolvability ross_adaptability ross_flexibility
                           ross_scalability ross_modifiability extensibility agility reactivity formReconfigurability
                           operationalReconfigurability functionalVersatility operationalVersatility exchangeability

}.
