(** * Car System Model *)

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

Inductive Who := manufacturer | dealer | owner | driver | passenger | mechanic | ai.

(** ** Resources for measuring cost-benefit *)

(** 
[Resources] is a framework for quantifying time, money, and other
elements of value that can be gained or lost as a result of a change.
*)

Inductive Resources := mkResources {
  timeMinutes: nat;
  moneyDollars: nat;
  wearRate: nat
}.

(** ** Phase *)

(**
[Phase] represents the lifecycle phases of a physical car product.
*)

Inductive Phase := manufacturing | customization | operation | repair.

(** ** Product state space *)

(**
We now present a model of the state space of a physical car as a
product of state spaces of component subsystems and situational
parameters.
*)

(** *** Oil *)

Inductive OilCleanliness := oilClean | oilDirty.

Inductive OilFullness := oilFull | oilLow | oilEmpty.

Inductive OilCondition := mkOilCondition { 
  oilCleanliness : OilCleanliness; 
  oilFullness: OilFullness }.

(** *** Tires *)

Inductive TireInflation := tireFull | tireLow | tireEmpty | tirePunctured.

(** *** Place *)

Inductive Place := factory | dealership | home | road | shop.


(** *** Overall State Space *)

Inductive CarState := mkCarState { 
  oilState: OilCondition ;
  tireState: TireInflation;
  placeState: Place;
  phaseState: Phase
}.

