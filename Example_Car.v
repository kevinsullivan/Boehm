Require Export System.
Require Export Changeable.
Require Export DesignStructure.
Require Import List.
Import ListNotations.

Inductive CarStakeholders := manufacturer | dealer | owner | driver | passenger | mechanic | ai.

Inductive CarValue := mk_car_value {
  timeMinutes: nat;
  moneyDollars: nat;
  gasolineGallons: nat;
  wearRate: nat
}.

Inductive CarPhases := manufacturing | sale | ownership.

Inductive CarContexts := factory | dealership | home | road | shop.


(** ** Model: Product state space *)

Inductive OilCleanliness := oil_clean | oil_dirty.
Inductive OilFullness := oil_full | oil_low | oil_empty.
Inductive OilCondition := mk_oil_condition { 
  oilCleanliness : OilCleanliness; 
  oilFullness: OilFullness
}.

Inductive Location := l_home | l_away.

Inductive TireInflation := tire_full | tire_low | tire_empty | tire_punctured.

Record ArtifactState : Set :=
  {
    oilState : OilCondition;
    tireState : TireInflation;
    location : Location }.

Inductive car_params := interior | exterior | engine | fuel_intake | chassis | wheel_axel.

Definition uses (p1 p2: car_params): Prop :=
  match p1, p2 with
      | engine, wheel_axel => True
      | engine, fuel_intake => True
      | _, _ => False
  end.

Definition satisfies (p1 p2: car_params): Prop :=
  False.

Definition encapsulates (p1 p2: car_params): Prop :=
  False.

Definition volatile (p: car_params): Prop :=
  match p with
      | interior => True
      | _ => False
  end.

Definition engine_module := {| elements := [engine; fuel_intake; wheel_axel]; name := "moves car" |}.
Definition interior_module := {| elements := [interior]; name := "interior" |}.

Definition modules: list (@Module car_params) := [engine_module; interior_module].

Definition car_dep: Dependency :=
  {| Modules := modules;
     Uses := uses;
     Satisfies := satisfies;
     Encapsulates := encapsulates;
     Volatile := volatile |}.

Inductive car_dep_type :=
  | mk_car_dep : forall d: Dependency, d = car_dep -> car_dep_type.

Definition extract_dep cdt :=
  match cdt with
      | mk_car_dep d _ => d
  end.

Inductive Car := mk_car { 
                     car_artifact: ArtifactState;
                     car_design: car_dep_type
                   }.

Definition CarSystemType := mk_system_type CarContexts CarStakeholders CarPhases Car CarValue.

(**
Abbreviations for writing propositions, assertions, actions.
 *)

Definition CarSystemState := @SystemInstance CarSystemType.

Definition CarAssertion := @Assertion CarSystemType.

Definition CarAction := @Action CarSystemType.

(**
Useful propositions
 *)

Definition isModular (cs: CarSystemState): Prop := modular (extract_dep (car_design (artifact cs))).

Definition oilLow (cs: CarSystemState): Prop := (oilFullness (oilState (car_artifact (artifact cs)))) = oil_low.
Definition oilFull (cs: CarSystemState): Prop := (oilFullness (oilState (car_artifact (artifact cs)))) = oil_full.
Definition oilClean (cs: CarSystemState): Prop := (oilCleanliness (oilState (car_artifact (artifact cs)))) = oil_clean.
Definition oilDirty (cs: CarSystemState): Prop := (oilCleanliness (oilState (car_artifact (artifact cs)))) = oil_dirty.
Definition atHome (cs: CarSystemState): Prop := (location (car_artifact (artifact cs)) = l_home).
Definition inOwnershipPhase (cs: CarSystemState) := Prop = ((phase cs) = ownership).

Definition oilLowState: CarAssertion   := fun cs: CarSystemState => oilLow cs.
Definition oilFullState: CarAssertion  := fun cs: CarSystemState => oilFull cs.
Definition oilCleanState: CarAssertion := fun cs: CarSystemState => oilClean cs.
Definition oilDirtyState: CarAssertion := fun cs: CarSystemState => oilDirty cs.
Definition oilFreshState: CarAssertion := fun cs: CarSystemState => oilClean cs /\ oilFull cs.
Definition anyState: CarAssertion      := fun cs: CarSystemState => True.
Definition atHomeState: CarAssertion   := fun cs: CarSystemState => atHome cs.

(**
The changeOil action yields a full tank of clean oil and makes no other changes.
We should FIX the failure to update the cost.
 *)

Definition ownerChangeOil: CarAction := 
  fun cs: CarSystemState => 
    mk_system CarSystemType 
              home 
              ownership
              {| car_artifact := {|  oilState := {| oilCleanliness := oil_clean; oilFullness := oil_full|};
                                     tireState := (tireState (car_artifact (artifact cs)));
                                     location := (location (car_artifact (artifact cs)))|};
                 car_design := mk_car_dep car_dep eq_refl|}
              (value cs).

(*

A complete specification might include a definition of the initial state
of the system, such as this one:

Definition initCar: SystemInstance := 
  mk_system 
    CarSystemType
    home
    ownership
    (mk_car 
      (mk_oil_condition oil_clean oil_full)
      tire_full
      l_home)
    (mk_car_value 0 0 0 0).

 *)