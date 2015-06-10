Require Export Changeable.
Require Export Example_Car.

(** * Car Changeability Properties *)

Definition oilLowProp (c: Car): Prop := (oilFullness (oilState c)) = oil_low.
Definition oilFullProp (c: Car): Prop := (oilFullness (oilState c)) = oil_full.
Definition oilCleanProp (c: Car): Prop := (oilCleanliness (oilState c)) = oil_clean.
Definition oilDirtyProp (c: Car): Prop := (oilCleanliness (oilState c)) = oil_dirty.

(** *** Useful assertions *)

Definition CarAssertion := @Assertion CarMetaSystem.
Definition CarAction := @Action CarMetaSystem.
Definition CarChange := @Change CarMetaSystem.
Definition CarValue := @Value CarMetaSystem.
Definition CarChangeRequirement := @ChangeRequirement CarMetaSystem.

Definition oilLowState: CarAssertion   := fun c: Car=> oilLowProp c.
Definition oilFullState: CarAssertion  := fun c: Car=> oilFullProp c.
Definition oilCleanState: CarAssertion := fun c: Car=> oilCleanProp c.
Definition oilDirtyState: CarAssertion := fun c: Car=> oilDirtyProp c.
Definition oilFreshState: CarAssertion := fun c: Car=> oilCleanProp c /\ oilFullProp c.
Definition anyState: CarAssertion      := fun c: Car => True.

(* Definition atHomeState: CarAssertion := fun c: Car => (location c) = l_home. *)

Definition changeOil: CarAction := 
  fun c: Car=>
    mk_car (mk_oil_condition oil_clean oil_full) (tireState c) l_home.

Definition homeOilChange: CarChange := mk_change oilDirtyState changeOil oilFreshState.

Theorem homeOilChangeValid: forall c: Car, (oilDirtyState c) -> oilFreshState (changeOil c).
intros. compute. auto. Qed.

Definition oilChangeValue (v: CarValue): Prop := 
    (timeMinutes (get_cost (cost v))) < 60 /\ 
    (wearRate (get_benefit (benefit v))) = 0.

Example oil_changeable_by_owner: CarChangeRequirement := mkChangeRequirement 
    oilDirtyState owner home ownership homeOilChange oilChangeValue.

Definition CarSystem := System CarMetaSystem.

(** Requirement-Specific Logic goes here *)
Inductive meets_requirement: CarSystem -> CarChangeRequirement -> Prop :=
  always: forall sys: CarSystem, forall req: ChangeRequirement, meets_requirement sys req.

(** *** Car System *)

Definition home_car: Car := mk_car (mk_oil_condition oil_dirty oil_low) tire_full l_home.
Definition away_car: Car := mk_car (mk_oil_condition oil_clean oil_full) tire_full l_away.

Definition home_car_system := mk_system CarMetaSystem home_car.
Definition away_car_system := mk_system CarMetaSystem away_car.

Inductive car_changeable: CarSystem -> Prop :=
| meets_all_requirements: forall sys: CarSystem, meets_requirement sys oil_changeable_by_owner /\ meets_requirement sys oil_changeable_by_owner ->
                                                 car_changeable sys.

Definition my_car_changeable: Changeable home_car_system.
Proof.
  constructor.
  exists car_changeable.
  apply home_changeable.
  apply always.
Qed.