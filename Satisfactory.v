(** * System Quality General Theory *)

(*
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross

March, 2015
*)
Add Rec LoadPath "./ContributeQA".

Require Export MissionEffective.
Require Export ResourceUtilization.
Require Export Dependable.
Require Export Flexible.
Require Export Affordable.
Require Export Resilient.

Class Satisfactory (System: Set) (Stakeholder: Set) (Context: Set) := {
      sys: System

    ; physicalCapability : System -> Stakeholder -> Context -> Prop 
    ; cyberCapability : System -> Stakeholder -> Context -> Prop
    ; humanUsability : System -> Stakeholder -> Context -> Prop
    ; speed : System -> Stakeholder -> Context -> Prop
    ; endurability : System -> Stakeholder -> Context -> Prop
    ; maneuverability : System -> Stakeholder -> Context -> Prop
    ; accuracy : System -> Stakeholder -> Context -> Prop
    ; impact : System -> Stakeholder -> Context -> Prop
    ; scalability : System -> Stakeholder -> Context -> Prop
    ; versability : System -> Stakeholder -> Context -> Prop
    ; interoperability : System -> Stakeholder -> Context -> Prop

    ; cost : System -> Context -> Prop
    ; duration : System -> Context -> Prop
    ; keyPersonnel : System -> Context -> Prop
    ; otherScareResources : System -> Context -> Prop
    ; manufacturability : System -> Context -> Prop
    ; sustainability : System -> Context -> Prop

    ; security : System -> Context -> Prop
    ; safety : System -> Context -> Prop
    ; reliability : System -> Context -> Prop
    ; maintainability : System -> Context -> Prop
    ; availability : System -> Context -> Prop
    ; survivability : System -> Context -> Prop
    ; robustness : System -> Context -> Prop

    ; modifiability : System -> Context -> Prop
    ; tailorability : System -> Context -> Prop
    ; adaptability : System -> Context -> Prop

    ; me: MissionEffective System Stakeholder Context sys physicalCapability cyberCapability humanUsability speed 
              endurability maneuverability accuracy impact scalability versability interoperability
    ; ru: ResourceUtilization System Context sys cost duration keyPersonnel otherScareResources manufacturability sustainability
    ; dp: Dependable System Context sys security safety reliability maintainability availability survivability robustness
    ; fl: Flexible System Context sys modifiability tailorability adaptability
    (* affordable is a composite property of "MissionEffective" and "ResourceUtilization"*)
    ; af: Affordable System Stakeholder Context sys 
              physicalCapability cyberCapability humanUsability speed 
              endurability maneuverability accuracy impact scalability versability interoperability
              cost duration keyPersonnel otherScareResources manufacturability sustainability
    (* Resillient is a composite property of "Dependable" and "Flexible"*)
    ; rs: Resilient System Context sys security safety reliability maintainability availability survivability robustness
                                       modifiability tailorability adaptability
}.
