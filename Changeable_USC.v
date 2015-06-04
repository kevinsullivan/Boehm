(**
"<who> needs to be able to change <what> <when> <why>"
*)


(**
When (trigger: the oil in the car gets dirty) (when: during extended operation) (who: the owner) should be able to 
(change: replace) (what: the oil)  (where: in the driveway) (amount: full amount) 
(how: replace_oil == remove stop; drain oil; replace filter; replace stop; add new oil)
(value: within an hour, for monetary cost of materials, to avoid engine damage).
*)

(**
When (trigger: the oil in the car gets dirty during extended operation) (who: the owner) should be able to 
(change: replace the oil)  (where: at home) 
(how: replace_oil == remove stop; drain oil; replace filter; replace stop; add new oil)
(value: within an hour, for monetary cost of materials, to avoid engine damage).
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

Inductive ChangeRequirement {State Who Where Resources: Set} : Type := 
  mkChangeRequirement {
      trigger: Assertion State
    ;  who: Who 
    ; change: Change State
    ; place: Where (* not sure we need this -- fold into change? *)
    ; value: Value Resources -> Prop
 }.

Arguments mkChangeRequirement {State Who Where Resources } trigger who change place value.

(*
We eliminate perturbation/trigger as its own state, replacing it with a "Change State" object.
Inductive CarTrigger := oilDirty | tireFlat | engineBlown | customerSelectsOptions.
*)

(** Interface into the larger hierarchy **)

Inductive Changeable_USC (System: Set) (Stakeholder: Set) (Context: Set) (Phase: Set) (sys: System): Prop := 
  satisfiesUSCChangeabilityRequirement:
    (exists change_usc: System -> Stakeholder -> Context -> Phase -> Prop,
       (forall cx: Context, forall sh: Stakeholder, forall ps: Phase, change_usc sys sh cx ps)) ->
    Changeable_USC System Stakeholder Context Phase sys.