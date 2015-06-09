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

(**
When (trigger: the oil in the car gets dirty) (when: during extended operation) (who: the owner) should be able to 
(change: replace) (what: the oil)  (where: in the driveway) (amount: full amount) 
(how: replace_oil == remove stop; drain oil; replace filter; replace stop; add new oil)
(value: within an hour, for monetary cost of materials, to avoid engine damage).
*)



Inductive CarPhase := manufacturing | customization | operation | repair.

Inductive CarWho := manufacturer | dealer | owner | driver | passenger | mechanic | ai.

Inductive CarOilCleanliness := oilClean | oilDirty.
Inductive CarOilFullness := oilFull | oilLow | oilEmpty.
Inductive CarOilState := mkCarOilState { 
  oilCleanliness: CarOilCleanliness; 
  oilFullness: CarOilFullness }.

Inductive CarTireInflation := tireFull | tireLow | tireEmpty | tirePunctured.

Inductive CarPlace := factory | dealership | home | road | shop.

Inductive CarState := mkCarState { 
  carOilState: CarOilState ;
  carTireState: CarTireInflation;
  carPlace: CarPlace;
  carPhase: CarPhase
}.

Definition oilIsLow (c: CarState): Prop := (oilFullness (carOilState c)) = oilLow.
Definition oilIsFull (c: CarState): Prop := (oilFullness (carOilState c)) = oilFull.
Definition oilIsClean (c: CarState): Prop := (oilCleanliness (carOilState c)) = oilClean.
Definition oilIsDirty (c: CarState): Prop := (oilCleanliness (carOilState c)) = oilDirty.
Definition inUsePhase (c: CarState): Prop := (carPhase c = operation \/ carPhase c = repair).
Definition atHome (c: CarState): Prop := (carPlace c = home).

Definition oilLowState: Assertion CarState := fun c: CarState => oilIsLow c.
Definition oilFullState: Assertion CarState := fun c: CarState => oilIsFull c.
Definition oilCleanState: Assertion CarState := fun c: CarState => oilIsClean c.
Definition oilDirtyState: Assertion CarState := fun c: CarState => oilIsDirty c.
Definition oilFreshState: Assertion CarState := fun c: CarState => oilIsClean c /\ oilIsFull c.
Definition inUseState: Assertion CarState := fun c: CarState => inUsePhase c.
Definition atHomeState: Assertion CarState := fun c: CarState => atHome c.
Definition anyState: Assertion CarState := fun c: CarState => True.

Definition changeOilAction: Action CarState := 
  fun c: CarState =>
    mkCarState (mkCarOilState oilClean oilFull) (carTireState c) (carPlace c) (carPhase c).

Definition homeOilChange: Change CarState := mkChange CarState atHomeState changeOilAction oilFreshState.

Theorem oilChangeWorks: forall s: CarState, (atHomeState s) -> oilFreshState (changeOilAction s).
intros. compute. auto. Qed.

Inductive CarResources := mkCarResources {
  carTimeMinutes: nat;
  carMoneyDollars: nat;
  carWearRate: nat
}.

Definition CarValue := Value CarResources.

(*
Inductive Value (Resources: Set) := mkValue {
  valueCost: Cost Resources;
  valueBenefit: Benefit Resources
}.
*)

Definition oilChangeValue (v: CarValue): Prop := 
    (carTimeMinutes (cost CarResources (valueCost CarResources v))) < 60 /\ 
    (carMoneyDollars (benefit CarResources (valueBenefit CarResources v))) = 0.

Example oil_changeable_by_owner := mkChangeRequirement 
    oilDirtyState owner homeOilChange home oilChangeValue.

Print oil_changeable_by_owner.

