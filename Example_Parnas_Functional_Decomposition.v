Require Import DesignStructure.
Import ListNotations.
Open Scope string_scope.

Module ExampleOne.

Inductive kwicParameter := computer | corpus | user | input_type | circ_type | alph_type | out_type | input_data | 
                                             circ_data | alph_data | out_data | input_alg | circ_alg | alph_alg | out_alg | master.

Definition uses (a b: kwicParameter) : Prop :=
  match a, b with
      | computer, (corpus | user) => True
      | user, corpus => True
      | input_alg, (input_data | user | corpus) => True
      | circ_alg, (input_data | circ_data | corpus | user) => True
      | alph_alg, (alph_data | input_data | circ_data
                   | computer | corpus | user) => True
      | out_alg, (input_data | alph_data | out_data
                   | computer | corpus) => True
      | input_data, (circ_data | alph_data
                   | computer | corpus) => True
      | circ_data, (input_data | alph_data
                   | computer | corpus) => True
      | alph_data, (input_data | circ_data
                    | computer | corpus) => True
      | out_data, (computer | corpus) => True
      | master, user => True
      | _, _ => False
  end.

Definition satisfies (a b: kwicParameter) : Prop :=
  match a, b with
      | input_alg, input_type => True
      | circ_alg, circ_type => True
      | alph_alg, alph_type => True
      | out_alg, out_type => True
      | _, _ => False
  end.

Definition encapsulates (a b : kwicParameter) : Prop := False.
  
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
       elements := []|}].

Definition kwic_dependency_1 := {|
                                 Modules := kwic_modules;
                                 Volatile := kwic_volatile;
                                 Uses:= uses;
                                 Satisfies:= satisfies;
                                 Encapsulates:= encapsulates
                               |}.

Theorem not_modular_kwic_1 : ~ modular kwic_dependency_1.
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H1.
  unfold satisfy_and_encapsulate_coupled in H2.
  unfold Satisfies in *. simpl in *.
  destruct H2 with (a := input_alg) (b := input_type).
  simpl. exact I.
Qed.

End ExampleOne.

Module ExampleTwo.

Inductive kwicParameter := computer | corpus | user | line_type| input_type | circ_type
                           | alph_type | out_type | line_data | input_data
                           | circ_data | alph_data | out_data | line_alg | input_alg
                           | circ_alg | alph_alg | out_alg | master.

Inductive uses : kwicParameter -> kwicParameter -> Prop :=
     | uses_computer_corpus: uses computer corpus
     | uses_computer_user: uses computer user
     | uses_user_corpus: uses user corpus
     | uses_lineDS_lineAlg: uses line_data line_alg
     | uses_lineAlg_lineDS: uses line_alg line_data
     | uses_inputDS_inputAlg: uses input_data input_alg
     | uses_inputAlg_inputDS: uses input_alg input_data
     | uses_circDS_circAlg: uses circ_data circ_alg
     | uses_circAlg_circDS: uses circ_alg circ_data
     | uses_alphDS_alphAlg: uses alph_data alph_alg
     | uses_alphAlg_alphDS: uses alph_alg alph_data
     | uses_outDS_outAlg: uses out_data out_alg
     | uses_outAlg_outDS: uses out_alg out_data
     | uses_master_lineType: uses master line_type
     | uses_master_inputType: uses master input_type
     | uses_master_circType: uses master circ_type
     | uses_master_alphType: uses master alph_type
     | uses_master_outType: uses master out_type
     | uses_master_user: uses master user
     | uses_inputAlg_lineType: uses input_alg line_type
     | uses_circDS_lineType: uses circ_data line_type
     | uses_circAlg_lineType: uses circ_alg line_type
     | uses_alphDS_lineType: uses alph_data line_type
     | uses_alphAlg_lineType: uses alph_alg line_type
     | uses_outAlg_lineType: uses out_alg line_type.


Inductive satisfies: kwicParameter -> kwicParameter -> Prop :=
    | satisfies_lineDS_lineType: satisfies line_data line_type
    | satisfies_inputDS_inputType: satisfies input_data input_type
    | satisfies_circDS_circType: satisfies circ_data circ_type
    | satisfies_alphDS_alphType: satisfies alph_data alph_type
    | satisfies_outDS_outType: satisfies out_data out_type
    | satisfies_lineAlg_lineType: satisfies line_alg line_type
    | satisfies_inputAlg_inputType: satisfies input_alg input_type
    | satisfies_circAlg_circType: satisfies circ_alg circ_type
    | satisfies_alphAlg_alphType: satisfies alph_alg alph_type
    | satisfies_outAlg_outType: satisfies out_alg out_type.

Inductive encapsulates: kwicParameter -> kwicParameter -> Prop :=
    | encapsulates_lineType_lineDS: encapsulates input_type line_data
    | encapsulates_inputType_inputDS: encapsulates input_type input_data
    | encapsulates_circType_circDS: encapsulates circ_type circ_data
    | encapsulates_alphType_alphDS: encapsulates alph_type alph_data
    | encapsulates_outType_outDS: encapsulates out_type out_data
    | encapsulates_lineType_lineAlg: encapsulates line_type line_alg
    | encapsulates_lineType_lineData: encapsulates line_type line_data
    | encapsulates_inputType_inputAlg: encapsulates input_type input_alg
    | encapsulates_circType_circAlg: encapsulates circ_type circ_alg
    | encapsulates_alphType_alphAlg: encapsulates alph_type alph_alg
    | encapsulates_outType_outAlg: encapsulates out_type out_alg.

Definition in_mod := {| name := "Input";
      elements := [input_data; input_alg; input_type]|}.
Definition line_mod := {| name := "Line";
       elements := [line_data; line_alg; line_type]|}.
Definition circ_mod := {| name := "Circular";
       elements := [circ_data; circ_alg; circ_type]|}.
Definition alph_mod := {| name := "Alphabetizer";
       elements := [alph_data; alph_alg; alph_type]|}.
Definition out_mod := {| name := "Output";
       elements := [out_data; out_alg; out_type]|}.
Definition env_mod := {| name := "Environment";
       elements := [user; computer; corpus; master]|}.

Definition kwic_modules : list (@Module kwicParameter) :=
  [in_mod; line_mod; circ_mod; alph_mod; out_mod; env_mod].

Definition kwic_volatile (p : kwicParameter): Prop :=
  match p with
    | corpus => True
    | computer => True
    | user => True
    | master => True
    | _ => False
  end.

Definition kwic_dependency := {|
                                 Modules := kwic_modules;
                                 Volatile := kwic_volatile;
                                 Uses:= uses;
                                 Satisfies:= satisfies;
                                 Encapsulates:= encapsulates
                               |}.

Hint Unfold separate_modules hides_volatility
     no_cross_module_circular_use no_circular_satisfaction satisfy_and_encapsulate_coupled.

Theorem modular_kwic_2 : modular kwic_dependency.
Proof.
  unfold modular.
  split.
  (* No Circular Satisfies *)
  unfold not, no_circular_satisfaction.
  intros.
  inversion H; subst; unfold not; unfold Satisfies in *; simpl in *; intros;
  match goal with
      | [ H : satisfies ?a ?b |- _] => inversion H
  end.
  split.
  (* Satisfy and Encapsulate Coupled *)
  unfold satisfy_and_encapsulate_coupled; intros.
  inversion H; subst; unfold not; unfold Encapsulates in *; simpl in *; intros;
  repeat constructor.

  (* No leak volatility *)
  unfold hides_volatility. intros.
  unfold not, separate_modules. intros.

  unfold Satisfies in H; simpl in H.
  destruct H.
  destruct a, b; inversion H.
  inversion H0; subst. inversion H1. inversion H2. inversion H2.
  inversion H0. subst. inversion H1. inversion H2. inversion H2.
  inversion H0. subst. inversion H1. inversion H2. inversion H2.
  inversion H0. subst. inversion H1. inversion H2. inversion H2.
  inversion H0. subst. inversion H1. inversion H2. inversion H2.
  inversion H0. subst. inversion H1. inversion H2. inversion H2.
  inversion H0. subst. inversion H1. inversion H2. inversion H2.
  inversion H0. subst. inversion H1. inversion H2. inversion H2.
  inversion H0. subst. inversion H1. inversion H2. inversion H2.
  inversion H0. subst. inversion H1. inversion H2. inversion H2.

  destruct H.
  exists env_mod; split; simpl; auto.
  exists env_mod; split; simpl; auto.
  exists env_mod; split; simpl; auto.
  exists line_mod; split; simpl; auto.
  exists line_mod; split; simpl; auto.
  exists in_mod; split; simpl; auto.
  exists in_mod; split; simpl; auto.
  exists circ_mod; split; simpl; auto.
  exists circ_mod; split; simpl; auto.
  exists alph_mod; split; simpl; auto.
  exists alph_mod; split; simpl; auto.
  exists out_mod; split; simpl; auto.
  exists out_mod; split; simpl; auto.
  inversion H0. inversion H. inversion H1. inversion H1.
  inversion H0. inversion H. inversion H1. inversion H1.
  inversion H0. inversion H. inversion H1. inversion H1.
  inversion H0. inversion H. inversion H1. inversion H1.
  inversion H0. inversion H. inversion H1. inversion H1.

  exists env_mod; split; simpl; auto.
  inversion H0. inversion H. inversion H1. inversion H1.
  inversion H0. inversion H. inversion H1. inversion H1.
  inversion H0. inversion H. inversion H1. inversion H1.
  inversion H0. inversion H. inversion H1. inversion H1.
  inversion H0. inversion H. inversion H1. inversion H1.
  inversion H0. inversion H. inversion H1. inversion H1.

Qed.

End ExampleTwo.