(** ** Context *)

Inductive kwicContexts := nominal.

(** ** Phase *)

(**
[kwicPhases] represents the lifecycle phases of a software system.
*)

(** design, implementation and maintenance are talked about in the paper*)
Inductive kwicPhases := design | implementation | maintenance.

(** ** Stakeholder *)

(**
[kwicStakeholders] represents the set of potential system change agents
*)

Inductive kwicStakeholders :=  developer | customer.

(** ** Value for measuring cost-benefit *)

(** 
[kwicValue] is a framework for quantifying time, money, and other
elements of value that can be gained or lost as a result of a change.
*)

Inductive kwicValue := mk_value { 
  modulesChanged: nat
}.

Inductive computerState := computer_pre | computer_post.
Inductive corpusState := corpus_pre | corpus_post.
Inductive userState := user_pre | user_post.

Record kwicVolatileState : Set := {
  computer_state: computerState;
  corpus_state: corpusState;
  user_state: userState
}.