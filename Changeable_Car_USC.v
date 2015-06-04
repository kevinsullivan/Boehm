Require Export Changeable_USC.
Require Export Car_USC.

(** * Car Changeability Properties *)

(**
We want to be able to formalize changeability requirements such as the following: "When the oil in
a car is dirty the owner should be able to execute a home oil change at home at a cost of less than
sixty minutes with the benefit of reducing the wear rate on the engine to approximately zero."
 *)

(**
Our approach is in two parts. First we construct a state-based model of the system and meta-system.
We import this model from Car_USC.s module.
 *)

(**
Then we write what amounts to a Hoare-Triple-based specifications of a change augmented with
additional elements such as the agent *who* should be  able to make a change, at what cost, and
with what benefits. To this end we import our generic module for Hoare-Triple-based changeability
specifications; we parameterize it with elements of our domain-specific Car model; and we extend
the results in the rest of this file to formalize the desired changeability property.
 *)

(** ** Hoare Triple *)

(**
We start by defining a Hoare Triple asserting that if the car is at home and if a [homeOilChange]
change action is performed then the state of the car will be the same as it was initially except that
the oil state will be fresh, which we defined to be a conjunction of full and clean.
 *)

(** *** Useful propositions *)

(**
Hoare triples are assertion-action-assertion triples. Assertions are built from propositions
about the states of a system before and after an action. Here we give names to propositions
that will (or could) be useful in writing assertions about the states of cars. As you can see in
the inUsePhaseProp proposition, one can use the full power of logic in writing propositions.
 *)

Definition oilLowProp (c: CarState): Prop := (oilFullness (oilState c)) = oilLow.
Definition oilFullProp (c: CarState): Prop := (oilFullness (oilState c)) = oilFull.
Definition oilCleanProp (c: CarState): Prop := (oilCleanliness (oilState c)) = oilClean.
Definition oilDirtyProp (c: CarState): Prop := (oilCleanliness (oilState c)) = oilDirty.
Definition inUsePhaseProp (c: CarState): Prop := (phaseState c = operation \/ phaseState c = repair).
Definition atHomeProp (c: CarState): Prop := (placeState c = home).


(** *** Useful assertions *)

(**
In Hoare logic, an assertion is a function that maps a state to a proposition about that
state, which might or might not be true. The basic form of reasoning is to prove that if
the assertion about the state before an action is true, that performing the action will
leave the system in a state in which the assertion about the state after the action is
true. That is, the precondition being true combined with the effect of the action makes
the post-condition true. (Here we ignore subtleties involved in non-termination.) The
assertions we define here mostly build from the propositions defined, and one of them
(oilFreshState) illustrates the use of logic to combine basic propositions into more
complex propositions for purposes of defining more complex assertions.
 *)

Definition oilLowState: Assertion CarState := fun c: CarState => oilLowProp c.
Definition oilFullState: Assertion CarState := fun c: CarState => oilFullProp c.
Definition oilCleanState: Assertion CarState := fun c: CarState => oilCleanProp c.
Definition oilDirtyState: Assertion CarState := fun c: CarState => oilDirtyProp c.
Definition oilFreshState: Assertion CarState := fun c: CarState => oilCleanProp c /\ oilFullProp c.
Definition inUseState: Assertion CarState := fun c: CarState => inUsePhaseProp c.
Definition atHomeState: Assertion CarState := fun c: CarState => atHomeProp c.
Definition anyState: Assertion CarState := fun c: CarState => True.


(** *** A change action (here, oil change) *)

(**
Hoare logic is used to specify and reason about the effects of actions on system states.
An action is a tranformer of system states. Here we model a [changeOil] action as an
function that takes a car state and that returns a new car state in which the oil condition
is clean and full and the rest of the car state is unchanged.
 *)

Definition changeOil: Action CarState :=
  fun c: CarState =>
    mkCarState (mkOilCondition oilClean oilFull) (tireState c) (placeState c) (phaseState c).

(** *** Building (and proving) the desired Hoare Triple *)

(**
We now construct the desired Hoare Triple. It models a transformation of a car state:
from a state in which the assertion that the car is at home is true, via the changeOil
action, to a state in which the assertion that the oil is fresh is true.
 *)

Definition homeOilChange: Change CarState := mkChange CarState atHomeState changeOil oilFreshState.

(**
Proving a Hoare Triple means showing that if the precondition is satisfied and the action
is performed, then the postcondition will be satisfied. It's obvious that that's the case here,
as the changeOil action clearly makes the oil fresh. If the change action were more complex,
e.g., involving a sequence of smaller actions, possibly with conditions and loops involved,
the validity of the triple might be less clear. In any case, we can formally prove validity if
it holds, and here is a simple example.
 *)

Definition homeOilChangeValid: Prop := forall s: CarState, (atHomeState s) -> oilFreshState (changeOil s).
Theorem homeOilChangeValid_pf: homeOilChangeValid.
  intros. compute. auto. Qed.

(** ** Value *)

(**
We now specialize the general notion of value to the car-specific domain, and write a
value proposition for the oil change behavior. Here is says that the change should cost
less than 60 minutes and 50 dollars
 *)

Definition CarValue := Value Resources.

Definition oilChangeValue (v: CarValue): Prop :=
  (timeMinutes (cost Resources (valueCost Resources v))) < 60 /\
  (wearRate (benefit Resources (valueBenefit Resources v))) = 0.

(** ** We can now package up all these elements into a Changeability requirement object *)

(**
When the oil is dirty the owner should be able to execute a home oil change at home at a cost of less than sixty
minutes with the benefit that the wear rate on the engine is reduced to zero.
 *)

Example oil_changeable_by_owner := mkChangeRequirement
                                     oilDirtyState owner homeOilChange home oilChangeValue.

Print oil_changeable_by_owner.

(** ** Evaluation *)

(**
This framework captures almost all of what can be expressed in the Ross framework.
One small exception is that we don't have an explicit model for transitory vs. enduring
disturbances.

On the positive side, unlike the Ross model, this framework supports and has an explicit
system model in terms of which changeability requirements are expressed. Like the Ross
model, it also has a generic component that pretty much corresponds to Ross's basis,
i.e., our Changeable_USC modules. Unlike the Ross model, our generic component is
paramterized by an arbitrary system model, here elemenst of our Car_USC model. Our
framework then not only separates the generic framework from the system model, but
also supports separate specification of system-specific changeability requirements: in
the Changeable_Car_USC module, in this case.

The principal benefit of this approach is that it allows for precise specification of what
changes in system state are required, what actions are to be used to achieve them,
what the pre- and post-conditions of those actions are, with proofs of effectiveness.
This framework also explicitly models who the players are in the domain, who must
be able to perform actions, what the units of cost and benefit are in the given domain,
and what the constraints are on cost and value of a given change.

The costs of using this approach include the need to write a system model, and to
formalize assertions, actions, and cost/benefit constraints. The benefit is an enormous
improvement in expressiveness and precision relative to Ross's framework.
 *)

Definition car_stakeholders := unit.
Definition car_context := unit.
Definition car_phases := unit.
Inductive car_models :=
  | oil_and_tire_model: car_models
  | other_models: car_models.

(** Here we define our "little c" changeability, the callback relation that plugs the
Changeability_USC framework into our hierarchy. For our purposes, one way to prove
that a car is changeable is to prove its oil is changeable. Another is to simply say so **)

Inductive changeability_usc (sys: car_models) (sh: car_stakeholders) (context: car_context)
          (phases: car_phases): Prop :=
  changeable_oil: homeOilChangeValid -> changeability_usc sys sh context phases.

Theorem car_is_USC_changeable: Changeable_USC car_models car_stakeholders car_context car_phases oil_and_tire_model.
Proof.
  apply satisfiesUSCChangeabilityRequirement. exists changeability_usc.
  intros. apply changeable_oil. apply homeOilChangeValid_pf.
Qed.