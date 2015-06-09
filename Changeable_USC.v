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

Inductive ChangeRequirement {State Who Resources: Set} : Type := 
  mkChangeRequirement {
      trigger: Assertion State
    ;  who: Who 
    ; change: Change State
    ; value: Value Resources -> Prop
 }.

Arguments mkChangeRequirement {State Who Resources} trigger who change value.

(*
We eliminate perturbation/trigger as its own state, replacing it with a "Change State" object.
Inductive CarTrigger := oilDirty | tireFlat | engineBlown | customerSelectsOptions.
*)

