Require Export System.
Require Export Changeable.

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
Inductive Car := mk_car { 
  oilState: OilCondition;
  tireState: TireInflation;
  location: Location 
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

Definition oilLow (cs: CarSystemState): Prop := (oilFullness (oilState (artifact cs))) = oil_low.
Definition oilFull (cs: CarSystemState): Prop := (oilFullness (oilState (artifact cs))) = oil_full.
Definition oilClean (cs: CarSystemState): Prop := (oilCleanliness (oilState (artifact cs))) = oil_clean.
Definition oilDirty (cs: CarSystemState): Prop := (oilCleanliness (oilState (artifact cs))) = oil_dirty.
Definition atHome (cs: CarSystemState): Prop := (location (artifact cs) = l_home).
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
        (context cs)
        (phase cs)
        (mk_car 
          (mk_oil_condition oil_clean oil_full) 
          (tireState (artifact cs)) 
          (location (artifact cs)))
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