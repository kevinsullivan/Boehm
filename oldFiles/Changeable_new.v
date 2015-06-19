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


Inductive Changeable (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop :=
  isChangeable:
    ValueRobust System Stakeholder Context Phase sys ->
    ValueSurvivable System Stakeholder Context Phase sys ->
    Ross_Robust System Stakeholder Context Phase sys ->
    ClassicalPassiveRobust System Stakeholder Context Phase sys ->
    Ross_Survivable System Stakeholder Context Phase sys ->
    Evolvable System Stakeholder Context Phase sys ->
    Ross_Adaptable System Stakeholder Context Phase sys ->
    Ross_Flexible System Stakeholder Context Phase sys ->
    Ross_Scalable System Stakeholder Context Phase sys ->
    Ross_Modifiable System Stakeholder Context Phase sys ->
    Extensible System Stakeholder Context Phase sys ->
    Agile System Stakeholder Context Phase sys ->
    Reactive System Stakeholder Context Phase sys ->
    FormReconfigurable System Stakeholder Context Phase sys ->
    OperationalReconfigurable System Stakeholder Context Phase sys ->
    FunctionalVersatile System Stakeholder Context Phase sys ->
    OperationalVersatile System Stakeholder Context Phase sys ->
    Exchangeable System Stakeholder Context Phase sys ->
    Changeable System Stakeholder Context Phase sys.