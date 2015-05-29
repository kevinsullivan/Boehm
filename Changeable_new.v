(** * Changeability General Theory *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes,
Barry Boehm, and Adam Ross

March, 2015
*)
Add Rec LoadPath "./Changeability".

Require Export ValueRobust.
Require Export ValueSurvivable.
Require Export Ross_Robust.
Require Export ClassicalPassiveRobust.
Require Export Ross_Survivable.
Require Export Evolvable.
Require Export Ross_Adaptable.
Require Export Ross_Flexible.
Require Export Ross_Scalable.
Require Export Ross_Modifiable.
Require Export Extensible.
Require Export Agile.
Require Export Reactive.
Require Export FormReconfigurable.
Require Export OperationalReconfigurable.
Require Export FunctionalVersatile.
Require Export OperationalVersatile.
Require Export Exchangeable.


Inductive Changeable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System) 
                     (valueRobustness: System -> Stakeholder -> Context -> Phase -> Prop)
                     (valueSurvivability: System -> Stakeholder -> Context -> Phase -> Prop)
                     (ross_robustness: System -> Stakeholder -> Context -> Phase -> Prop)
                     (classicalPassiveRobustness: System -> Stakeholder -> Context -> Phase -> Prop)
                     (ross_survivability: System -> Stakeholder -> Context -> Phase -> Prop)
                     (evolvability: System -> Stakeholder -> Context -> Phase -> Prop)
                     (ross_adaptability: System -> Stakeholder -> Context -> Phase -> Prop)
                     (ross_flexibility: System -> Stakeholder -> Context -> Phase -> Prop)
                     (ross_scalability: System -> Stakeholder -> Context -> Phase -> Prop)
                     (ross_modifiability: System -> Stakeholder -> Context -> Phase -> Prop)
                     (extensibility: System -> Stakeholder -> Context -> Phase -> Prop)
                     (agility: System -> Stakeholder -> Context -> Phase -> Prop)
                     (reactivity: System -> Stakeholder -> Context -> Phase -> Prop)
                     (formReconfigurability: System -> Stakeholder -> Context -> Phase -> Prop)
                     (operationalReconfigurability: System -> Stakeholder -> Context -> Phase -> Prop)
                     (functionalVersatility: System -> Stakeholder -> Context -> Phase -> Prop)
                     (operationalVersatility: System -> Stakeholder -> Context -> Phase -> Prop)
                     (exchangeability: System -> Stakeholder -> Context -> Phase -> Prop)
                     : Prop :=
  isChangeable:
    ValueRobust System Stakeholder Context Phase sys valueRobustness ->
    ValueSurvivable System Stakeholder Context Phase sys valueSurvivability ->
    Ross_Robust System Stakeholder Context Phase sys ross_robustness ->
    ClassicalPassiveRobust System Stakeholder Context Phase sys classicalPassiveRobustness ->
    Ross_Survivable System Stakeholder Context Phase sys ross_survivability ->
    Evolvable System Stakeholder Context Phase sys evolvability ->
    Ross_Adaptable System Stakeholder Context Phase sys ross_adaptability ->
    Ross_Flexible System Stakeholder Context Phase sys ross_flexibility ->
    Ross_Scalable System Stakeholder Context Phase sys ross_scalability ->
    Ross_Modifiable System Stakeholder Context Phase sys ross_modifiability ->
    Extensible System Stakeholder Context Phase sys extensibility ->
    Agile System Stakeholder Context Phase sys agility ->
    Reactive System Stakeholder Context Phase sys reactivity ->
    FormReconfigurable System Stakeholder Context Phase sys formReconfigurability ->
    OperationalReconfigurable System Stakeholder Context Phase sys operationalReconfigurability ->
    FunctionalVersatile System Stakeholder Context Phase sys functionalVersatility ->
    OperationalVersatile System Stakeholder Context Phase sys operationalVersatility ->
    Exchangeable System Stakeholder Context Phase sys exchangeability ->
    Changeable System Stakeholder Context Phase sys valueRobustness valueSurvivability ross_robustness
               classicalPassiveRobustness ross_survivability evolvability ross_adaptability ross_flexibility
               ross_scalability ross_modifiability extensibility agility reactivity formReconfigurability
               operationalReconfigurability functionalVersatility operationalVersatility exchangeability.
