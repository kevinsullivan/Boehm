Require Export DesignStructure.
Import ListNotations.
Open Scope string_scope.
Require Export System.
Require Export Changeable.

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


Inductive kwicParameter := computer | corpus | user
                             | line_abs | line_alg | line_data
                             | alph_abs | alph_alg | alph_data
                             | circ_abs | circ_alg | circ_data
                             | input_abs | input_alg | input_data
                             | output_abs | output_alg | output_data
                             | master.

Definition uses (a b: kwicParameter): Prop :=
    match a, b with
      | master, (line_abs | input_abs | circ_abs | alph_abs | output_abs) => True
      | line_alg, line_data => True
      | line_data, line_alg  => True
      | input_alg, (input_data | line_abs) => True
      | input_data, input_alg  => True
      | circ_alg, (circ_data  | line_abs) => True
      | circ_data, (circ_alg  | line_abs) => True
      | alph_alg, (alph_data | line_abs) => True
      | alph_data, (alph_alg | line_abs)  => True
      | output_alg, (output_data | line_abs)  => True
      | output_data, output_alg  => True
      | _, _ => False
    end.

  Definition satisfies (a b: kwicParameter): Prop :=
    match b, a with
      | computer,  (line_data | line_alg | input_data | circ_data | alph_data | alph_alg | output_data | output_alg)=> True
      | corpus,  (line_data | line_alg | input_data | input_alg | circ_data | circ_alg | alph_data | alph_alg | output_data | output_alg)=> True
      | user, (input_alg | circ_alg | alph_alg | master) => True
      | line_abs, (line_data | line_alg) => True
      | input_abs, (input_data | input_alg) => True
      | circ_abs, (circ_data | circ_alg) => True
      | alph_abs, (alph_data | alph_alg) => True
      | output_abs, (output_data | output_alg) => True
      | _, _ => False
    end.

Definition input_mod := {| name := "Input";
      elements := [input_data; input_alg; input_abs]|}.
Definition line_mod := {| name := "Line";
       elements := [line_data; line_alg; line_abs]|}.
Definition circ_mod := {| name := "Circular";
       elements := [circ_data; circ_alg; circ_abs]|}.
Definition alph_mod := {| name := "Alphabetizer";
       elements := [alph_data; alph_alg; alph_abs]|}.
Definition out_mod := {| name := "Output";
       elements := [output_data; output_alg; output_abs]|}.
Definition master_mod :=  {| name := "Master";
       elements := [master]|}.
Definition env_mod := {| name := "Environment";
       elements := [user; computer; corpus]|}.

Definition kwic_modules : list (@Module kwicParameter) :=
  [input_mod; line_mod; circ_mod; alph_mod; out_mod; master_mod; env_mod].

Definition kwic_volatile (p : kwicParameter): Prop :=
  match p with
    | corpus => True
    | computer => True
    | user => True
    | _ => False
  end.

Definition kwic_ds: DesignStructure := {|
                                 Modules := kwic_modules;
                                 Volatile := kwic_volatile;
                                 Uses:= uses;
                                 Satisfies:= satisfies
                               |}.

Inductive kwic_ds_type := 
    | mk_kwic_ds : forall ds: DesignStructure, ds = kwic_ds -> kwic_ds_type.

Definition extract_kwic_ds kdt :=
  match kdt with
    | mk_kwic_ds ds _ => ds
  end.

Inductive kwic := mk_kwic {
  kwic_volatile_state: kwicVolatileState;
  kwic_design: kwic_ds_type
}.

Definition kwicSystemType := mk_system_type kwicContexts kwicStakeholders kwicPhases kwic kwicValue.

(**
Abbreviations for writing propositions, assertions, actions.
*)

Definition kwicSystemState := @SystemInstance kwicSystemType.

Definition kwicAssertion := @Assertion kwicSystemType.

Definition kwicAction := @Action kwicSystemType.

(*test more specifically whether a system is modular with respect to a single parameter*)
Definition isModular (ks: kwicSystemState): Prop := modular (extract_kwic_ds (kwic_design (artifact ks))).
Definition satisfiesModularity_wrt (kp: kwicParameter) (ks: kwicSystemState): Prop := modular_wrt kp (extract_kwic_ds (kwic_design (artifact ks))).

Definition computerPre (ks: kwicSystemState): Prop := computer_state (kwic_volatile_state (artifact ks)) = computer_pre.
Definition computerPost (ks: kwicSystemState): Prop := computer_state (kwic_volatile_state (artifact ks)) = computer_post.
Definition corpusPre (ks: kwicSystemState): Prop := corpus_state (kwic_volatile_state (artifact ks)) = corpus_pre.
Definition corpusPost (ks: kwicSystemState): Prop := corpus_state (kwic_volatile_state (artifact ks)) = corpus_post.
Definition userPre (ks: kwicSystemState): Prop := user_state (kwic_volatile_state (artifact ks)) = user_pre.
Definition userPost (ks: kwicSystemState): Prop := user_state (kwic_volatile_state (artifact ks)) = user_post.
Definition inMaintenancePhase (ks: kwicSystemState): Prop := phase ks = maintenance.

Definition computerPreState : kwicAssertion := fun ks: kwicSystemState => computerPre ks.
Definition computerPostState : kwicAssertion := fun ks: kwicSystemState => computerPost ks.
Definition corpusPreState : kwicAssertion := fun ks: kwicSystemState => corpusPre ks.
Definition corpusPostState : kwicAssertion := fun ks: kwicSystemState => corpusPost ks.
Definition userPreState : kwicAssertion := fun ks: kwicSystemState => userPre ks.
Definition userPostState : kwicAssertion := fun ks: kwicSystemState => userPost ks.

Definition costomerChangeCorpus: kwicAction :=
  fun ks: kwicSystemState =>
      mk_system kwicSystemType
                         nominal
                         maintenance
                         {| kwic_volatile_state := {|  computer_state := computer_state (kwic_volatile_state (artifact ks));
                                                                   corpus_state:= corpus_post;
                                                                   user_state:= user_state (kwic_volatile_state (artifact ks))
                                                               |};
                            kwic_design := mk_kwic_ds kwic_ds eq_refl |}
                          (value ks).
