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

    ; mission_effective: MissionEffective System Stakeholder Context Phase sys physicalCapability cyberCapability humanUsability speed
              endurability maneuverability accuracy impact scalability versability interoperability
    ; resource_utilization: ResourceUtilization System Stakeholder Context Phase sys cost duration keyPersonnel otherScareResources manufacturability sustainability
    ; dependable: Dependable System Stakeholder Context Phase sys security safety reliability maintainability availability survivability robustness
    ; flexible: Flexible System Stakeholder Context Phase sys modifiability tailorability adaptability
    (* affordable is a composite property of "MissionEffective" and "ResourceUtilization"*)
    ; affordable: Affordable System Stakeholder Context Phase sys
              physicalCapability cyberCapability humanUsability speed
              endurability maneuverability accuracy impact scalability versability interoperability
              cost duration keyPersonnel otherScareResources manufacturability sustainability
    (* Resilient is a composite property of "Dependable" and "Flexible" *)
    ; resilient: Resilient System Stakeholder Context Phase sys security safety reliability maintainability availability survivability robustness
              modifiability tailorability adaptability
}.
