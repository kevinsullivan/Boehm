(** * KWIC System  *)

Require Export System.

(** ** Context *)

Inductive Context := nominal.

(** ** Phase *)

(**
[Phase] represents the lifecycle phases of a software system.
*)

(** design, implementation and maintenance are talked about in the paper*)
Inductive Phase := requirements | design | implementation | testing | deployment | maintenance.

(** ** Stakeholder *)

(**
[Stakeholder] represents the set of potential system change agents
*)

Inductive Stakeholder :=  developer | customer.

(** ** Resources for measuring cost-benefit *)

(** 
[Resources] is a framework for quantifying time, money, and other
elements of value that can be gained or lost as a result of a change.
*)

Inductive Value := mkValue {
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

(** ** Likely changes *)

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

Definition KWICSystem (kwic: KWIC) (val: Value): System := mk_sys Context Stakeholder Phase KWIC Value kwic val.
