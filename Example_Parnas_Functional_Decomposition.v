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

Definition encapsulates (a b : kwicParameter) : Prop :=
  match a, b with
    | input_type, input_alg => True
    | circ_type, circ_alg => True
    | alph_type, alph_alg => True
    | out_type, out_alg => True
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
  inversion H3.
  apply H4.
  unfold cross_module_circular_use.
  exists circ_data, input_data.
  clear; intros.
  unfold Uses in *. simpl in *.
  unfold separate_modules.
  intros.
  destruct m1, m2.
  inversion H1; inversion H2.
  inversion H5; inversion H6; subst.
  contradiction.
  inversion H5
  

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
     | uses_lineDS_computer: uses line_data computer
     | uses_inputDS_computer: uses input_data computer
     | uses_circDS_computer: uses circ_data computer
     | uses_alphDS_computer: uses alph_data computer
     | uses_outDS_computer: uses out_data computer
     | uses_lineDS_corpus: uses line_data corpus
     | uses_inputDS_corpus: uses input_data corpus
     | uses_circDS_corpus: uses circ_data corpus
     | uses_alphDS_corpus: uses alph_data corpus
     | uses_outDS_corpus: uses out_data corpus
     | uses_lineAlg_computer: uses line_alg computer
     | uses_alphAlg_computer: uses alph_alg computer
     | uses_outAlg_computer: uses out_alg computer
     | uses_lineAlg_corpus: uses line_alg corpus
     | uses_inputAlg_corpus: uses input_alg corpus
     | uses_circAlg_corpus: uses circ_alg corpus
     | uses_alphAlg_corpus: uses alph_alg corpus
     | uses_outAlg_corpus: uses out_alg corpus
     | uses_inputAlg_user: uses input_alg user
     | uses_circAlg_user: uses circ_alg user
     | uses_alphAlg_user: uses alph_alg user
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
    | encapsulates_inputType_inputAlg: encapsulates input_type input_alg
    | encapsulates_circType_circAlg: encapsulates circ_type circ_alg
    | encapsulates_alphType_alphAlg: encapsulates alph_type alph_alg
    | encapsulates_outType_outAlg: encapsulates out_type out_alg.

Definition kwic_modules : list (@Module kwicParameter) :=
  [{| name := "Input";
      elements := [input_data; input_alg]|};
    {| name := "Circular";
       elements := [circ_data; circ_alg]|};
    {| name := "Alphabetizer";
       elements := [alph_data; alph_alg]|};
    {| name := "Output";
       elements := [out_data; out_alg]|}].

Definition kwic_volatile (p : kwicParameter): Prop :=
  match p with
    | corpus => True
    | computer => True
    | user => True
    | _ => False
  end.

Definition kwic_dependency := {|
                                 Modules := kwic_modules;
                                 Volatile := kwic_volatile;
                                 Uses:= uses;
                                 Satisfies:= satisfies;
                                 Encapsulates:= encapsulates
                               |}.

(* Hint Unfold modular separate_modules leaks_volatility *)
(*      cross_module_circular_use circular_satisfaction satisfy_and_encapsulate_coupled. *)

Theorem modular_kwic_2 : modular kwic_dependency.
Proof.
  unfold modular.
  split.
  (* No Circular Satisfies *)
  unfold not, circular_satisfaction.
  intros; destruct H; destruct H.
  unfold Satisfies in H.
  simpl in H.
  destruct x, x0. 


  


  (* Satisfy and Encapsulate Coupled *)

  (* No Cross Module Circular Use *)

  (* No leak volatility *)

Abort.

End ExampleTwo.