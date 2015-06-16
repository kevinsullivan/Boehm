Require Export Changeable.
Require Export Example_Parnas.

(** * KWIC Changeability Properties *)

Definition inputFormatOneProp (k: KWIC): Prop := (inputFormat k) = input_format_one.
Definition inputFormatAnotherProp (k: KWIC): Prop := (inputFormat k) = input_format_another.
Definition LineStorageAllInCoreProp (k: KWIC): Prop := (lineStorage k) = line_storage_all_in_core.
Definition LineStoragePartialInCoreProp (k: KWIC): Prop := (lineStorage k) = line_storage_partial_in_core.
Definition WordPackFourProp (k: KWIC): Prop := (wordPack k) = word_pack_four.
Definition WordPackNoneProp (k: KWIC): Prop := (wordPack k) = word_pack_none.
Definition WordPackDiffFormatProp (k: KWIC): Prop := (wordPack k) = word_pack_diff_format.
Definition CircularShifterWithIndexProp (k: KWIC): Prop := (circularShifter k) = circular_shift_with_index.
Definition CircularShifterWithoutIndexProp (k: KWIC): Prop := (circularShifter k) = circular_shift_without_index.
Definition AlphabetizeOnceProp (k: KWIC): Prop := (alphabetizer k) = alphabetize_once.
Definition SearchWhenNeededProp (k: KWIC): Prop := (alphabetizer k) = search_when_needed.
Definition AlphabetizePartiallyProp (k: KWIC): Prop := (alphabetizer k) =  alphabetize_partially.

(** *** Useful assertions *)

Definition KWICAssertion := @Assertion KWICSystem.
Definition KWICAction := @Action KWICSystem.
Definition KWICChange := @Change KWICSystem.
Definition KWICValue := @Value KWICSystem.
Definition KWICChangeRequirement := @ChangeRequirement KWICSystem.

(** *** States *)
Definition inputFormatOneState: KWICAssertion   := fun k: KWIC=> inputFormatOneProp k.
Definition inputFormatAnotherState: KWICAssertion  := fun k: KWIC=> inputFormatAnotherProp k.
Definition LineStorageAllInCoreState: KWICAssertion := fun k: KWIC=> LineStorageAllInCoreProp k.
Definition LineStoragePartialInCoreState: KWICAssertion := fun k: KWIC=> LineStoragePartialInCoreProp k.
Definition WordPackFourState: KWICAssertion   := fun k: KWIC=> WordPackFourProp k.
Definition WordPackNoneState: KWICAssertion  := fun k: KWIC=> WordPackNoneProp k.
Definition WordPackDiffFormatState: KWICAssertion := fun k: KWIC=> WordPackDiffFormatProp k.
Definition CircularShifterWithIndexState: KWICAssertion := fun k: KWIC=> CircularShifterWithIndexProp k.
Definition CircularShifterWithoutIndexState: KWICAssertion   := fun k: KWIC=> CircularShifterWithoutIndexProp k.
Definition AlphabetizeOnceState: KWICAssertion  := fun k: KWIC=> AlphabetizeOnceProp k.
Definition SearchWhenNeededState: KWICAssertion := fun k: KWIC=> SearchWhenNeededProp k.
Definition AlphabetizePartiallyState: KWICAssertion := fun k: KWIC=> AlphabetizePartiallyProp k.

(** *** Changes *)

(** Input  Format Change*)
Definition changeInputFormat: KWICAction := 
  fun k: KWIC=>
    mk_kwic (interactivePerformance k) input_format_another (lineStorage k) (wordPack k) (circularShifter k) (alphabetizer k).

Definition inputFormatChange: KWICChange := mk_change inputFormatOneState changeInputFormat inputFormatAnotherState.

Definition inputFormatChangeValue (v: KWICValue): Prop := 
    (modules v) = 1 /\ 
    (developers v) < 4 /\
    (interfaces v) < 5 /\
    (developmentTime v) < 7 /\
    (satisfaction v) > 3 /\
    (dollars v) > 100.

Example input_format_changeable_by_customer: KWICChangeRequirement := mkChangeRequirement 
    inputFormatOneState customer nominal maintenance  inputFormatChange inputFormatChangeValue.

(** Line Storage Change*)
Definition changeLineStorage: KWICAction := 
  fun k: KWIC=>
    mk_kwic (interactivePerformance k) (inputFormat k) (line_storage_all_in_core) (wordPack k) (circularShifter k) (alphabetizer k).

Definition lineStorageChange: KWICChange := mk_change LineStorageAllInCoreState changeLineStorage LineStoragePartialInCoreState.

Definition lineStorageChangeValue (v: KWICValue): Prop := 
    (modules v) = 1 /\ 
    (developers v) < 4 /\
    (interfaces v) < 5 /\
    (developmentTime v) < 14 /\
    (runtime v) < 100 /\
    (memory v) < 100 /\
    (satisfaction v) > 3 /\
    (dollars v) > 100.

Example line_storage_changeable_by_developer: KWICChangeRequirement := mkChangeRequirement 
    LineStorageAllInCoreState developer nominal testing  lineStorageChange lineStorageChangeValue.

(** Requirement-Specific Logic goes here *)
Inductive meets_requirement: KWICSystem -> KWICChangeRequirement -> Prop :=
  always: forall sys: KWICSystem, forall req: ChangeRequirement, meets_requirement sys req.

(** *** KWIC System *)

Definition my_kwic: KWIC := mk_kwic input_format_one line_storage_all_in_core word_pack_four circular_shift_with_index alphabetize_once.

Definition my_kwic_system := mk_system KWICMetaSystem my_kwic.


Inductive kwic_changeable: KWICSystem -> Prop := 
| meets_all_requirements: forall sys: KWICSystem, meets_requirement sys input_format_changeable_by_customer /\ 
                                                                                  meets_requirement sys line_storage_changeable_by_developer ->
                                                                                  kwic_changeable sys.

Definition my_kwic_changeable: Changeable my_kwic_system.
Proof.
  constructor.
  exists kwic_changeable.
  apply meets_all_requirements.
  split.
  apply always.
  apply always.
Qed.