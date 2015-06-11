Require Export Changeable.
Require Export Example_Parnas.

(** * Software Changeability Properties *)

Definition inputSizeSmallProp (s: Software): Prop := (inputSize (input s)) = input_size_small.
Definition inputSizeLargeProp (s: Software): Prop := (inputSize (input s)) = input_size_large.
Definition masterControlEfficiencyLowProp (s: Software): Prop := (masterControlEfficiency (masterControl s)) = master_control_efficiency_low.
Definition masterControlEfficiencyHighProp (s: Software): Prop := (masterControlEfficiency (masterControl s)) = master_control_efficiency_high.

(** *** Useful assertions *)

Definition SoftwareAssertion := @Assertion SoftwareMetaSystem.
Definition SoftwareAction := @Action SoftwareMetaSystem.
Definition SoftwareChange := @Change SoftwareMetaSystem.
Definition SoftwareValue := @Value SoftwareMetaSystem.
Definition SoftwareChangeRequirement := @ChangeRequirement SoftwareMetaSystem.

Definition inputSizeSmallState: SoftwareAssertion   := fun s: Software=> inputSizeSmallProp s.
Definition inputSizeLargeState: SoftwareAssertion  := fun s: Software=> inputSizeLargeProp s.
Definition masterControlEfficiencyLowState: SoftwareAssertion := fun s: Software=> masterControlEfficiencyLowProp s.
Definition masterControlEfficiencyHighState: SoftwareAssertion := fun s: Software=> masterControlEfficiencyHighProp s.

(** *** Changes *)

(** Input Change*)
Definition changeInput: SoftwareAction := 
  fun s: Software=>
    mk_software (mk_input input_format_csv input_size_large) (masterControl s).

Definition inputChange: SoftwareChange := mk_change inputSizeSmallState changeInput inputSizeLargeState.

Definition inputChangeValue (v: SoftwareValue): Prop := 
    (changedModules (get_cost (cost v))) = 1 /\ 
    (involvedDevelopers (get_cost (cost v))) < 4 /\
    (usedAPIs (get_cost (cost v))) < 5 /\
    (timeDays (get_cost (cost v))) < 7 /\
    (moneyDollars (get_benefit (benefit v))) > 100.

Example input_changeable_by_user: SoftwareChangeRequirement := mkChangeRequirement 
    inputSizeSmallState user general implementation  inputChange inputChangeValue.

(** Master Control Change*)
Definition changeMasterControl: SoftwareAction := 
  fun s: Software=>
    mk_software (input s) (mk_master_control master_control_efficiency_low master_control_errors_few).

Definition masterControlChange: SoftwareChange := mk_change masterControlEfficiencyLowState changeMasterControl masterControlEfficiencyHighState.

Definition masterControlChangeValue (v: SoftwareValue): Prop := 
    (changedModules (get_cost (cost v))) = 1 /\ 
    (involvedDevelopers (get_cost (cost v))) < 5 /\
    (usedAPIs (get_cost (cost v))) < 5 /\
    (timeDays (get_cost (cost v))) < 14 /\
    (improvedEfficiency (get_benefit (benefit v))) > 15.

Example master_control_changeable_by_developer: SoftwareChangeRequirement := mkChangeRequirement 
    masterControlEfficiencyLowState developer general implementation  masterControlChange masterControlChangeValue.

Definition SoftwareSystem := System SoftwareMetaSystem.

(** Requirement-Specific Logic goes here *)
Inductive meets_requirement: SoftwareSystem -> SoftwareChangeRequirement -> Prop :=
  always: forall sys: SoftwareSystem, forall req: ChangeRequirement, meets_requirement sys req.

(** *** Software System *)

Definition my_software: Software := mk_software (mk_input input_format_csv input_size_small) 
                                                                               (mk_master_control master_control_efficiency_low master_control_errors_few).

Definition my_software_system := mk_system SoftwareMetaSystem my_software.


Inductive software_changeable: SoftwareSystem -> Prop := 
| meets_all_requirements: forall sys: SoftwareSystem, meets_requirement sys input_changeable_by_user /\ 
                                                                                      meets_requirement sys master_control_changeable_by_developer ->
                                                                                      software_changeable sys.

Definition my_software_changeable: Changeable my_software_system.
Proof.
  constructor.
  exists software_changeable.
  apply meets_all_requirements.
  split.
  apply always.
  apply always.
Qed.