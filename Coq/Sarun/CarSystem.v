Require Import System.
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

Record Car : Set := mk_car
  {
    oilState : OilCondition;
    tireState : TireInflation;
    location : Location }.

Definition CarSystemType := mk_system_type CarContexts CarStakeholders CarPhases Car CarValue.

Definition CarSystemState := @SystemInstance CarSystemType.