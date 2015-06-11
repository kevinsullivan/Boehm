(** * Software System  *)

Require Export System.

(** ** Stakeholder *)

(**
[Stakeholder] represents the set of potential system change agents
*)

Inductive Stakeholder :=  investor | manager | developer | maintainer | tester | user.

(** ** Resources for measuring cost-benefit *)

(** 
[Resources] is a framework for quantifying time, money, and other
elements of value that can be gained or lost as a result of a change.
*)

Inductive Resource := mkResources {
  codeLines: nat;
  changedModules: nat;
  usedAPIs: nat;
  involvedDevelopers: nat;
  moneyDollars: nat;
  improvedEfficiency: nat;
  timeDays: nat
}.

(** ** Phase *)

(**
[Phase] represents the lifecycle phases of a software system.
*)

Inductive Phase := requirements | design | implementation | testing | deployment | maintenance.

(** *** Context *)

Inductive Context := circumstantial | general.


(** ** Model: Product state space *)

(**
We now present a model of the state space of a software system as a
product of state spaces of component subsystems and situational
parameters..
*)

(** *** Input *)
Inductive InputFormat := input_format_txt | input_format_csv | input_format_binary_code.
Inductive InputSize := input_size_large | input_size_small.

Inductive Input:= mk_input { 
  inputFormat: InputFormat;
  inputSize: InputSize
}.

(** *** Master Control *)

Inductive MasterControlEfficiency := master_control_efficiency_high | master_control_efficiency_medium | master_control_efficiency_low.
Inductive MasterControlErrors := master_control_errors_many | master_control_errors_few | master_control_errors_none.

Inductive MasterControl := mk_master_control {
  masterControlEfficiency: MasterControlEfficiency;
  masterControlErrors: MasterControlErrors
}.

Inductive Software := mk_software { 
  input: Input;
  masterControl: MasterControl
}.

Definition SoftwareMetaSystem: MetaSystem := mk_msys Stakeholder Resource Phase Context Software.
