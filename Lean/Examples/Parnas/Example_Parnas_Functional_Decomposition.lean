import Examples.Parnas.DesignStructure
import System.System
import Qualities.Changeable
import Examples.Parnas.Example_Parnas_Shared_Info

inductive kwicParameter | computer | corpus | user
                        | alph_abs | alph_alg | alph_data
                        | circ_abs | circ_alg | circ_data
                        | input_abs | input_alg | input_data
                        | output_abs | output_alg | output_data
                        | master
                        
open kwicParameter

--TODO
-- error: maximum number of steps (128) exceeded 
definition uses : kwicParameter -> kwicParameter -> Prop
| kwicParameter.master kwicParameter.input_abs := true
| kwicParameter.master kwicParameter.circ_abs := true
| kwicParameter.master kwicParameter.alph_abs := true
| kwicParameter.master kwicParameter.output_abs := true
| kwicParameter.input_alg kwicParameter.input_data := true
| kwicParameter.input_data kwicParameter.circ_data := true
| kwicParameter.input_data kwicParameter.alph_data := true
| kwicParameter.circ_alg kwicParameter.circ_data := true
/-| kwicParameter.circ_alg kwicParameter.input_data := true
| kwicParameter.circ_data kwicParameter.input_data := true
| kwicParameter.circ_data kwicParameter.alph_data := true
| kwicParameter.alph_alg kwicParameter.input_data := true
| kwicParameter.alph_alg kwicParameter.circ_data := true
| kwicParameter.alph_alg kwicParameter.alph_data := true
| kwicParameter.alph_data kwicParameter.input_data := true
| kwicParameter.alph_data kwicParameter.circ_data := true
| kwicParameter.output_alg kwicParameter.input_data := true
| kwicParameter.output_alg kwicParameter.alph_data := true
| kwicParameter.output_alg kwicParameter.output_data := true-/
| _ _ := false

--TODO
-- error: maximum number of steps (128) exceeded 
definition satisfies : kwicParameter -> kwicParameter -> Prop
| computer  input_data := true
| computer  circ_data := true
| computer  alph_data := true
| computer  output_data := true
| computer  input_alg := true
| computer  alph_alg := true
| computer  output_alg := true
/-corpus  input_data := true
| corpus  input_alg := true
| corpus  circ_data := true
| corpus  circ_alg := true
| corpus  alph_data := true
| corpus  alph_alg := true
| corpus  output_data := true
| corpus  output_alg := true
| user circ_alg := true
| user alph_alg := true
| user master := true
| input_abs input_alg := true
| circ_abs circ_alg := true
| alph_abs alph_alg := true
| output_abs output_alg := true-/
| _ _ := false

definition input_mod : (@Module kwicParameter) := 
{ name := "Input", elements := []}

definition circ_mod : (@Module kwicParameter) := 
{ name := "Circular", elements := []}

definition alph_mod : (@Module kwicParameter) := 
{ name := "Alphabetizer", elements := []}

definition out_mod : (@Module kwicParameter) := 
{ name := "Output", elements := []}

definition master_mod : (@Module kwicParameter) := 
{ name := "Master", elements := []}

definition kwic_modules : list Module :=
[input_mod, circ_mod, alph_mod, out_mod, master_mod]

definition kwic_volatile : kwicParameter -> Prop
| corpus := true
| computer := true
| user := true
| _ := false

definition kwic_ds: DesignStructure := 
{ Modules := kwic_modules, Volatile := kwic_volatile, Uses:= uses, Satisfies:= satisfies }

inductive kwic_ds_type 
| mk_kwic_ds : forall (ds: DesignStructure), ds = kwic_ds -> kwic_ds_type

-- TODO
--definition extract_kwic_ds : kwic_ds_type -> DesignStructure
--| (kwic_ds_type.mk_kwic_ds) ds _ := ds

record kwic := 
mk :: (kwic_volatile_state: kwicVolatileState) (kwic_design: kwic_ds_type)

definition kwicSystemType : SystemType := { Contexts:=kwicContexts, Stakeholders:= kwicStakeholders, Phases:= kwicPhases, ArtifactType:= kwic, ValueType:= kwicValue }

/-
Abbreviations for writing propositions, assertions, actions.
-/

definition kwicSystemState := @SystemInstance kwicSystemType

definition kwicAssertion := @Assertion kwicSystemType

definition kwicAction := @Action kwicSystemType

/- test more specifically whether a system is modular with respect to a single parameter-/
--TODO
--definition isModular (ks: kwicSystemState): Prop := modular (extract_kwic_ds (kwic_design (artifact ks)))
--definition isModular_wrt (kp: kwicParameter) (ks: kwicSystemState): Prop := modular_wrt kp (extract_kwic_ds (kwic_design (artifact ks)))

definition computerPre (ks: kwicSystemState): Prop := ks^.artifact^.kwic_volatile_state^.computer_state = computerState.computer_pre
definition computerPost (ks: kwicSystemState): Prop := ks^.artifact^.kwic_volatile_state^.computer_state = computerState.computer_post
definition corpusPre (ks: kwicSystemState): Prop := ks^.artifact^.kwic_volatile_state^.corpus_state = corpusState.corpus_pre
definition corpusPost (ks: kwicSystemState): Prop := ks^.artifact^.kwic_volatile_state^.corpus_state = corpusState.corpus_post
definition userPre (ks: kwicSystemState): Prop := ks^.artifact^.kwic_volatile_state^.user_state = userState.user_pre
definition userPost (ks: kwicSystemState): Prop := ks^.artifact^.kwic_volatile_state^.user_state = userState.user_post
definition inMaintenancePhase (ks: kwicSystemState): Prop := ks^.phase = kwicPhases.maintenance

definition computerPreState : kwicAssertion := fun ks: kwicSystemState, computerPre ks
definition computerPostState : kwicAssertion := fun ks: kwicSystemState, computerPost ks
definition corpusPreState : kwicAssertion := fun ks: kwicSystemState, corpusPre ks
definition corpusPostState : kwicAssertion := fun ks: kwicSystemState,corpusPost ks
definition userPreState : kwicAssertion := fun ks: kwicSystemState, userPre ks
definition userPostState : kwicAssertion := fun ks: kwicSystemState, userPost ks

definition costomerChangeCorpus: kwicAction :=
  fun ks: kwicSystemState,
      { context:=kwicContexts.nominal,
        phase:=kwicPhases.maintenance,
        artifact:=
            { kwic_volatile_state := 
                {   computer_state := ks^.artifact^.kwic_volatile_state^.computer_state,
                    corpus_state:= corpusState.corpus_post,
                    user_state:= ks^.artifact^.kwic_volatile_state^.user_state },
              -- TODO
              --kwic_design := mk_kwic_ds kwic_ds eq_refl |}
              kwic_design := ks^.artifact^.kwic_design},
        value := ks^.value }