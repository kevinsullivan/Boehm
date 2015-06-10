Require Export System.

(** * Car System  *)

(**
We factor a car system model into this separate file, so that in principle 
it can be reused in stating many system properties. The system model 
in this case elements well beyond the physical product, including, for
example, the location of a car, and agents involved in manufacturing, 
selling, operating, and repairing a car.
*)

(** ** Who *)

(**
[Who] represents the set of potential system change agents
*)

Inductive Stakeholder := manufacturer | dealer | owner | driver | passenger | mechanic | ai.

(** ** Resources for measuring cost-benefit *)

(** 
[Resources] is a framework for quantifying time, money, and other
elements of value that can be gained or lost as a result of a change.
*)

Inductive Resource := mkResources {
  timeMinutes: nat;
  moneyDollars: nat;
  gasolineGallons: nat;
  wearRate: nat
}.

(** ** Phase *)

(**
[Phase] represents the lifecycle phases of a physical car product.
*)

Inductive Phase := manufacturing | sale | ownership.

(** *** Place *)

Inductive Context := factory | dealership | home | road | shop.


(** ** Model: Product state space *)

(**
We now present a model of the state space of a physical car as a
product of state spaces of component subsystems and situational
parameters.
*)

(** *** Oil *)

Inductive OilCleanliness := oil_clean | oil_dirty.
Inductive OilFullness := oil_full | oil_low | oil_empty.

Inductive OilCondition := mk_oil_condition { 
  oilCleanliness : OilCleanliness; 
  oilFullness: OilFullness
}.

Inductive Location := l_home | l_away.

(** *** Tires *)

Inductive TireInflation := tire_full | tire_low | tire_empty | tire_punctured.

Inductive Car := mk_car { 
  oilState: OilCondition;
  tireState: TireInflation;
  location: Location 
}.

Definition CarMetaSystem : MetaSystem := mk_msys Stakeholder Resource Phase Context Car.
