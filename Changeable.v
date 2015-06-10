(**
"<who> needs to be able to change <what> <when> <why>"
*)

Inductive Cost (Resources: Set) := mkCost {
  cost: Resources
}.

Inductive Benefit (Resources: Set) := mkBenefit {
  benefit: Resources
}.

Inductive Value (Resources: Set) := mkValue {
  valueCost: Cost Resources;
  valueBenefit: Benefit Resources
}.

Definition Assertion (State: Set) := State -> Prop.

Definition Action (State: Set) := State -> State.

Inductive Change (State: Set) := mkChange {
  changePrecondition: Assertion State;
  changeAction: Action State;
  changePostcondition: Assertion State
}.


Inductive ChangeRequirement {Stakeholder Resources State: Set} : Type := 
  mkChangeRequirement {
      trigger: Assertion State
    ;  sh: Stakeholder 
    ; change: Change State
    ; value: Value Resources -> Prop
 }.

Arguments mkChangeRequirement {Stakeholder Resources State} trigger sh change value.

Require Export System.

Inductive Changeable {model: Model} (sys: System model) : Prop :=
  satisfiesChangeabilityRequirement:
    (exists changeable: System model -> Prop, changeable sys) ->
    Changeable sys.
