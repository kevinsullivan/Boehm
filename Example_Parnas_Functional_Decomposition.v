Require Export DesignStructure.
Import ListNotations.
Open Scope string_scope.
Require Export System.
Require Export Changeable.
Require Export Example_Parnas_Shared_Info.

Inductive kwicParameter := computer | corpus | user
                             | alph_abs | alph_alg | alph_data
                             | circ_abs | circ_alg | circ_data
                             | input_abs | input_alg | input_data
                             | output_abs | output_alg | output_data
                             | master.

Definition uses (a b: kwicParameter): Prop :=
    match a, b with
      | master, (input_abs | circ_abs | alph_abs | output_abs) => True
      | input_alg, input_data  => True
      | input_data, (circ_data | alph_data) => True
      | circ_alg, (circ_data  | input_data) => True
      | circ_data, (input_data  | alph_data) => True
      | alph_alg, (input_data | circ_data | alph_data) => True
      | alph_data, (input_data | circ_data)  => True
      | output_alg, (input_data | alph_data | output_data)  => True
      | _, _ => False
    end.

Definition satisfies (a b: kwicParameter): Prop :=
    match b, a with
      | computer,  (input_data | circ_data | alph_data | output_data | input_alg | alph_alg | output_alg)=> True
      | corpus,  (input_data | circ_data | alph_data | output_data | input_alg | circ_alg | alph_alg | output_alg)=> True
      | user, (circ_alg | alph_alg | master) => True
      | input_abs, input_alg => True
      | circ_abs, circ_alg => True
      | alph_abs, alph_alg => True
      | output_abs, output_alg => True
      | _, _ => False
    end.


Definition kwic_volatile (p : kwicParameter): Prop :=
    match p with
      | corpus => True
      | computer => True
      | user => True
      | _ => False
    end.

Definition kwic_modules : list (@Module kwicParameter) :=
    [{| name := "Input";
        elements := [] |};
      {| name := "Circular";
         elements := []|};
      {| name := "Alphabetizer";
         elements := []|};
      {| name := "Output";
         elements := []|};
      {| name := "Master";
         elements := []|}].

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