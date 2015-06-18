(** * KWIC System  *)

Require Export System.
Require Export Changeable.

(** ** Context *)

Inductive KWICContexts := nominal.

(** ** Phase *)

(**
[Phase] represents the lifecycle phases of a software system.
*)

(** design, implementation and maintenance are talked about in the paper*)
Inductive KWICPhases := requirements | design | implementation | testing | deployment | maintenance.

(** ** Stakeholder *)

(**
[Stakeholder] represents the set of potential system change agents
*)

Inductive KWICStakeholders :=  developer | customer.

(** ** Resources for measuring cost-benefit *)

(** 
[Resources] is a framework for quantifying time, money, and other
elements of value that can be gained or lost as a result of a change.
*)

Inductive KWICValue := mkValue {
  linesOfCode: nat;
  modules: nat;
  interfaces: nat;
  developers: nat;
  dollars: nat;
  memory: nat;
  space: nat;
  runtime: nat;
  satisfaction: nat;
  developmentTime: nat
}.

(** ** Likely change variables*)

(**
There are a number of design decisions which are questionable and likely to change under many circumstances.
This a partial list.
*)

(** Input format *)

Inductive InputFormat := input_format_one | input_format_another.

(** 
The decision to have all lines stored in core. For large jobs it may prove inconvenient or imppractical to keep
all of the lines in core at any one time.
*)

Inductive LineStorage := line_storage_all_in_core | line_storage_partial_in_core.

(**
The desicion to pack the characters four to a word. In cases where we are working with small amounts of data 
it may prove undesirable to pack the characters; time will be saved by a character per word layout. In other cases,
we may pack, but in different formats.
*)

Inductive WordPack := word_pack_four | word_pack_none | word_pack_diff_format.

(**
The decision to make an index for the circular shifts rather that actually store them as such. Again for a small index 
or a large core, writing them out may be the preferable approach.
*)

Inductive CircularShifter := circular_shift_with_index | circular_shift_without_index.


(**
The desicion to alphabetize the list once, rather than either(a) search for each item when needed, or (b) partially alphabetize
as is done in Hoare's FIND. In a number of circumstance it would be advantageous to distribute the computation involved in 
alphabetization over the time required to produce the index.
*)

Inductive Alphabetizer := alphabetize_once | search_when_needed | alphabetize_partially.

(** Let us revisit the issue of design decisions VS changes of customer requirements*)
Inductive KWIC := mk_kwic { 
(* requirements *)
  interactivePerformance: bool;
  inputFormat: InputFormat;
(* design *)
  lineStorage: LineStorage;
  wordPack: WordPack;
  circularShifter: CircularShifter;
  alphabetizer: Alphabetizer
}.

Definition KWICSystemType := mk_system_type KWICContexts KWICStakeholders KWICPhases KWIC KWICValue.

(**
Abbreviations for writing propositions, assertions, actions.
*)

Definition KWICSystemState := @SystemInstance KWICSystemType.

Definition KWICAssertion := @Assertion KWICSystemType.

Definition KWICAction := @Action KWICSystemType.

(** * Useful propositions *)

Definition inputFormatOne (ks: KWICSystemState): Prop := (inputFormat (artifact ks)) = input_format_one.
Definition inputFormatAnother (ks: KWICSystemState): Prop := (inputFormat (artifact ks)) = input_format_another.
Definition LineStorageAllInCore (ks: KWICSystemState): Prop := (lineStorage (artifact ks)) = line_storage_all_in_core.
Definition LineStoragePartialInCore (ks: KWICSystemState): Prop := (lineStorage (artifact ks)) = line_storage_partial_in_core.
Definition WordPackFour (ks: KWICSystemState): Prop := (wordPack (artifact ks)) = word_pack_four.
Definition WordPackNone (ks: KWICSystemState): Prop := (wordPack (artifact ks)) = word_pack_none.
Definition WordPackDiffFormat (ks: KWICSystemState): Prop := (wordPack (artifact ks)) = word_pack_diff_format.
Definition CircularShifterWithIndex (ks: KWICSystemState): Prop := (circularShifter (artifact ks)) = circular_shift_with_index.
Definition CircularShifterWithoutIndex (ks: KWICSystemState): Prop := (circularShifter (artifact ks)) = circular_shift_without_index.
Definition AlphabetizeOnce (ks: KWICSystemState): Prop := (alphabetizer (artifact ks)) = alphabetize_once.
Definition SearchWhenNeeded (ks: KWICSystemState): Prop := (alphabetizer (artifact ks)) = search_when_needed.
Definition AlphabetizePartially (ks: KWICSystemState): Prop := (alphabetizer (artifact ks)) =  alphabetize_partially.

Definition inMaintenancePhase (ks: KWICSystemState): Prop := (phase ks) = maintenance.

(** *** States *)
Definition inputFormatOneState: KWICAssertion   := fun ks: KWICSystemState=> inputFormatOne ks.
Definition inputFormatAnotherState: KWICAssertion  := fun ks: KWICSystemState=> inputFormatAnother ks.
Definition LineStorageAllInCoreState: KWICAssertion := fun ks: KWICSystemState=> LineStorageAllInCore ks.
Definition LineStoragePartialInCoreState: KWICAssertion := fun ks: KWICSystemState=> LineStoragePartialInCore ks.
Definition WordPackFourState: KWICAssertion   := fun ks: KWICSystemState=> WordPackFour ks.
Definition WordPackNoneState: KWICAssertion  := fun ks: KWICSystemState=> WordPackNone ks.
Definition WordPackDiffFormatState: KWICAssertion := fun ks: KWICSystemState=> WordPackDiffFormat ks.
Definition CircularShifterWithIndexState: KWICAssertion := fun ks: KWICSystemState=> CircularShifterWithIndex ks.
Definition CircularShifterWithoutIndexState: KWICAssertion   := fun ks: KWICSystemState=> CircularShifterWithoutIndex ks.
Definition AlphabetizeOnceState: KWICAssertion  := fun ks: KWICSystemState=> AlphabetizeOnce ks.
Definition SearchWhenNeededState: KWICAssertion := fun ks: KWICSystemState=> SearchWhenNeeded ks.
Definition AlphabetizePartiallyState: KWICAssertion := fun ks: KWICSystemState=> AlphabetizePartially ks.

Definition customerChangeImputFormat: KWICAction :=
    fun ks: KWICSystemState =>
      mk_system KWICSystemType
         (context ks)
         (phase ks)
         (mk_kwic
           (interactivePerformance (artifact ks)) 
            input_format_another
           (lineStorage (artifact ks))
           (wordPack (artifact ks))
           (circularShifter (artifact ks))
           (alphabetizer (artifact ks)))
          (value ks).
