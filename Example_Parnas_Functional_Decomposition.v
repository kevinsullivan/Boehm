Require Import DesignStructure.
Import ListNotations.
Open Scope string_scope.

Module ExampleOne.

  Inductive kwicParameter := computer | corpus | user
                             |  input_data
                             | circ_data | alph_data | out_data | input_alg | circ_alg | alph_alg | out_alg | master.

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
                                   Satisfies:= satisfies |}.

  Theorem not_modular_kwic_1 : ~ modular kwic_dependency_1.
  Proof.
    unfold not.
    intros.
    inversion H.
    inversion H1.
    unfold hides_volatility in H3.
    specialize H3 with (a := computer) (b := corpus).
    simpl in H3.
    intuition.
    unfold same_module in H3.
    destruct H3.
    constructor. constructor.
    simpl in H3.
    destruct x.
    (** I'll finish this monday, once we have the computational model it'll be much easier to do this *)
Admitted.
End ExampleOne.

Module ExampleTwo.

  Inductive kwicParameter := computer | computer_abs | computer_impl
                             | corpus | corpus_abs | corpus_impl
                             | user | user_abs | user_impl
                             | line_abs | line_alg | line_data
                             | alph_abs | alph_alg | alph_data
                             | circ_abs | circ_alg | circ_data
                             | input_abs | input_alg | input_data
                             | output_abs | output_alg | output_data
                             | master.

  Definition uses (a b: kwicParameter): Prop :=
    match a, b with
      | master, (line_abs | input_abs | circ_abs | alph_abs | output_abs | user_abs | corpus_abs | computer_abs) => True
      | line_alg, line_data  => True
      | line_data, line_alg  => True
      | circ_alg, circ_data  => True
      | circ_data, circ_alg  => True
      | alph_alg, alph_data  => True
      | alph_data, alph_alg  => True
      | input_alg, input_data  => True
      | input_data, input_alg  => True
      | output_alg, output_data  => True
      | output_data, output_alg  => True
      | _, _ => False
    end.

  Definition satisfies (a b: kwicParameter): Prop :=
    match b, a with
      | computer_abs, computer_impl => True
      | corpus_abs, (corpus_impl | input_abs) => True
      | user_abs, user_impl => True
      | line_abs, (line_data | line_alg) => True
      | circ_abs, (circ_data | circ_alg) => True
      | alph_abs, (alph_data | alph_alg) => True
      | input_abs, (input_data | input_alg) => True
      | output_abs, (output_data | output_alg) => True
      | _, _ => False
    end.

  Definition in_mod := {| name := "Input";
                          elements := [input_data; input_alg; input_abs]|}.
  Definition line_mod := {| name := "Line";
                            elements := [line_data; line_alg; line_abs]|}.
  Definition circ_mod := {| name := "Circular";
                            elements := [circ_data; circ_alg; circ_abs]|}.
  Definition alph_mod := {| name := "Alphabetizer";
                            elements := [alph_data; alph_alg; alph_abs]|}.
  Definition out_mod := {| name := "Output";
                           elements := [output_data; output_alg; output_abs]|}.
  Definition env_mod := {| name := "Environment";
                           elements := [user; computer; corpus
                                       ; user_abs ; computer_abs; corpus_abs
                                       ; user_impl ; computer_impl ; corpus_impl]|}.

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
                                 Satisfies:= satisfies
                               |}.

  Hint Unfold separate_modules hides_volatility
       no_cross_module_circular_use no_circular_satisfaction.


  Theorem modular_kwic_2 : modular kwic_dependency.
  Proof.
    unfold modular.
    (* No Circular Satisfies *) split.
    unfold not, no_circular_satisfaction.
    intros. destruct a, b; auto.
    (* cross_module_circular_use *) split.
    unfold no_cross_module_circular_use; intros.
    unfold Uses in *; simpl in *.
    destruct a, b; auto; unfold not, separate_modules; intros.
    (* Todo finish this automation *)
    (* repeat match goal with *)
    (*     | [ H : forall m : Module, _ |- False ] => specialize H with (m := line_mod); destruct H; simpl; auto 7 *)
    (*     | [ H : forall m : Module, _ |- False ] => specialize H with (m := alph_mod); destruct H; simpl; auto 7 *)
    (*     | [ H : forall m : Module, _ |- False ] => specialize H with (m := circ_mod); destruct H; simpl; auto 7 *)
    (*     | [ H : forall m : Module, _ |- False ] => specialize H with (m := in_mod); destruct H; simpl; auto 7 *)
    (*     | [ H : forall m : Module, _ |- False ] => specialize H with (m := out_mod); destruct H; simpl; auto 7 *)
    (*        end.  *)
    specialize H1 with (m := line_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := line_mod).
    destruct H1; simpl; auto 7.
    specialize H1 with (m := alph_mod).
    destruct H1; simpl; auto 7.
    specialize H1 with (m := alph_mod).
    destruct H1; simpl; auto 7.
    specialize H1 with (m := circ_mod).
    destruct H1; simpl; auto 7.
    specialize H1 with (m := circ_mod).
    destruct H1; simpl; auto 7.
    specialize H1 with (m := in_mod).
    destruct H1; simpl; auto 7.
    specialize H1 with (m := in_mod).
    destruct H1; simpl; auto 7.
    specialize H1 with (m := out_mod).
    destruct H1; simpl; auto 7.
    specialize H1 with (m := out_mod).
    destruct H1; simpl; auto 7.

    (* No leak volatility *)
    unfold hides_volatility. intros.
    unfold same_module.
    simpl in H.
    destruct H.
    destruct a, b; inversion H.
    exists env_mod; intros; simpl; auto 20.
    exists env_mod; intros; simpl; auto 20.
    exists env_mod; intros; simpl; auto 20.
    exists line_mod; intros; simpl; auto 20.
    exists line_mod; intros; simpl; auto 20.
    exists alph_mod; intros; simpl; auto 20.
    exists alph_mod; intros; simpl; auto 20.
    exists circ_mod; intros; simpl; auto 20.
    exists circ_mod; intros; simpl; auto 20.


    inversion H0; subst; clear H0.
    inversion H1. destruct b; inversion H2.
    simpl in H2. destruct b; inversion H2.

    exists in_mod; intros; simpl; auto 20.
    exists in_mod; intros; simpl; auto 20.
    exists out_mod; intros; simpl; auto 20.
    exists out_mod; intros; simpl; auto 20.

    destruct a, b; inversion H.
    exists line_mod; intros; simpl; auto 20.
    exists line_mod; intros; simpl; auto 20.
    exists alph_mod; intros; simpl; auto 20.
    exists alph_mod; intros; simpl; auto 20.
    exists circ_mod; intros; simpl; auto 20.
    exists circ_mod; intros; simpl; auto 20.
    exists in_mod; intros; simpl; auto 20.
    exists in_mod; intros; simpl; auto 20.
    exists out_mod; intros; simpl; auto 20.
    exists out_mod; intros; simpl; auto 20.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.
   
    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

   inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2. 

   inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.
      
    inversion H1; subst. simpl in *. inversion H3.
    simpl in *. inversion H4.
    simpl in *.
    destruct b; inversion H4.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.
  Qed.

  Theorem modular_wrt_corpus: modular_wrt corpus kwic_dependency. 
    Proof.
      unfold modular_wrt.
      unfold modular.
      split.
      simpl.
      unfold no_circular_satisfaction.
      intros.
      destruct a, b; inversion H; auto.

      split.
    unfold no_cross_module_circular_use; intros.
    unfold Uses in *; simpl in *.
    destruct a, b; auto; unfold not, separate_modules; intros.
    specialize H1 with (m := line_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := line_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := alph_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := alph_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := circ_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := circ_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := in_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := in_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := out_mod);
    destruct H1; simpl; auto 9.
    specialize H1 with (m := out_mod);
    destruct H1; simpl; auto 9.

    unfold hides_volatility. intros.
    unfold same_module.
    simpl in H.
    destruct H.
    destruct a, b; inversion H.
    exists env_mod; intros; simpl; auto 20.
    exists env_mod; intros; simpl; auto 20.
    exists env_mod; intros; simpl; auto 20.
    exists line_mod; intros; simpl; auto 20.
    exists line_mod; intros; simpl; auto 20.
    exists alph_mod; intros; simpl; auto 20.
    exists alph_mod; intros; simpl; auto 20.
    exists circ_mod; intros; simpl; auto 20.
    exists circ_mod; intros; simpl; auto 20.


    inversion H0; subst; clear H0.
    simpl in H1. inversion H1.
    simpl in H2. inversion H2.
    simpl in *. destruct b; inversion H2.

    exists in_mod; intros; simpl; auto 20.
    exists in_mod; intros; simpl; auto 20.
    exists out_mod; intros; simpl; auto 20.
    exists out_mod; intros; simpl; auto 20.

    destruct a, b; inversion H.
    exists line_mod; intros; simpl; auto 20.
    exists line_mod; intros; simpl; auto 20.
    exists alph_mod; intros; simpl; auto 20.
    exists alph_mod; intros; simpl; auto 20.
    exists circ_mod; intros; simpl; auto 20.
    exists circ_mod; intros; simpl; auto 20.
    exists in_mod; intros; simpl; auto 20.
    exists in_mod; intros; simpl; auto 20.
    exists out_mod; intros; simpl; auto 20.
    exists out_mod; intros; simpl; auto 20.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

    inversion H0; subst. inversion H1. simpl in *.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.
   
    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

   inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.
    
    inversion H1; subst. simpl in *. inversion H3.
    simpl in *. inversion H4.
    simpl in *.
    destruct b; inversion H4.

    inversion H0; subst. inversion H1.
    simpl in H2. inversion H2.
    simpl in H2. destruct b; inversion H2.

    Qed.

End ExampleTwo.