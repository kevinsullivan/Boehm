import Changeable

inductive CarStakeholders : Type
| manufacturer 
| dealer 
| owner 
| driver 
| passenger 
| mechanic 
| ai

record CarValue := 
mk :: (timeMinutes: nat)
      (moneyDollars: nat)
      (gasolineGallons: nat)
      (wearRate: nat)

inductive CarPhases : Type
| manufacturing 
| sale 
| ownership

inductive CarContexts : Type 
| factory 
| dealership 
| home 
| road 
| shop

/- Model: Product state space -/

inductive OilCleanliness : Type
| oil_clean 
| oil_dirty

inductive OilFullness : Type
| oil_full 
| oil_low 
| oil_empty

record OilCondition := 
mk :: (oilCleanliness : OilCleanliness) 
      (oilFullness: OilFullness)

inductive Location : Type
| l_home 
| l_away

inductive TireInflation  : Type
| tire_full 
| tire_low 
| tire_empty 
| tire_punctured

record Car := 
mk :: (oilState : OilCondition) 
      (tireState : TireInflation)
      (location : Location)

def CarSystemType : SystemType :=
{Contexts := CarContexts, Stakeholders := CarStakeholders, Phases := CarPhases, ArtifactType := Car, ValueType := CarValue}

/-
Abbreviations for writing propositions, assertions, actions.
-/

definition CarSystemState := @SystemInstance CarSystemType

definition CarAssertion := @Assertion CarSystemType

definition CarAction := @Action CarSystemType

/-
Useful propositions
-/

definition oilLow (cs: CarSystemState): Prop := cs^.artifact^.oilState^.oilFullness = OilFullness.oil_low
definition oilFull (cs: CarSystemState): Prop := cs^.artifact^.oilState^.oilFullness = OilFullness.oil_full
definition oilClean (cs: CarSystemState): Prop := cs^.artifact^.oilState^.oilCleanliness = OilCleanliness.oil_clean
definition oilDirty (cs: CarSystemState): Prop := cs^.artifact^.oilState^.oilCleanliness = OilCleanliness.oil_dirty
definition atHome (cs: CarSystemState): Prop := cs^.artifact^.location = Location.l_home
definition inOwnershipPhase (cs: CarSystemState): Prop := cs^.phase = CarPhases.ownership

definition oilLowState: CarAssertion   := fun cs: CarSystemState, (oilLow cs)
definition oilFullState: CarAssertion  := fun cs: CarSystemState, oilFull cs
definition oilCleanState: CarAssertion := fun cs: CarSystemState, oilClean cs
definition oilDirtyState: CarAssertion := fun cs: CarSystemState, oilDirty cs
definition oilFreshState: CarAssertion := fun cs: CarSystemState, oilClean cs /\ oilFull cs
definition anyState: CarAssertion      := fun cs: CarSystemState, true
definition atHomeState: CarAssertion := fun cs: CarSystemState, atHome cs

/-
The changeOil action yields a full tank of clean oil and makes no other changes.
-/

definition ownerChangeOil: CarAction := 
  fun cs: CarSystemState,
      { context := cs^.context,
        phase := cs^.phase,
        artifact :=
        {
          oilState := {
            oilCleanliness := OilCleanliness.oil_clean,
            oilFullness := OilFullness.oil_full
          },
          tireState := cs^.artifact^.tireState,
          location := cs^.artifact^.location
        },
	value := cs^.value }
