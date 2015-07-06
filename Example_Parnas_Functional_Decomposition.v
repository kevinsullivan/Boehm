Require Import DesignStructure.

Inductive kwicParameter := computer | corpus | user | input_type | circ_type | alph_type | out_type | input_data | 
                                             circ_data | alph_data | out_data | input_alg | circ_alg | alph_alg | out_alg | master.

Inductive uses : kwicParameter -> kwicParameter -> Prop :=
     | uses_computer_corpus: uses computer corpus
     | uses_computer_user: uses computer user
     | uses_user_corpus: uses user corpus
     | uses_inputAlg_inputDS: uses input_alg input_data
     | uses_circAlg_inputDS: uses circ_alg input_data
     | uses_circAlg_circDS: uses circ_alg circ_data
     | uses_alphAlg_alphDS: uses alph_alg alph_data
     | uses_alphAlg_inputDS: uses alph_alg input_data
     | uses_alphAlg_circDS: uses alph_alg circ_data
     | uses_outAlg_inputDS: uses out_alg input_data
     | uses_outAlg_alphDS: uses out_alg alph_data
     | uses_outAlg_outDS: uses out_alg out_data
     | uses_inputDS_computer: uses input_data computer
     | uses_circDS_computer: uses circ_data computer
     | uses_alphDS_computer: uses alph_data computer
     | uses_outDS_computer: uses out_data computer
     | uses_inputDS_corpus: uses input_data corpus
     | uses_circDS_corpus: uses circ_data corpus
     | uses_alphDS_corpus: uses alph_data corpus
     | uses_outDS_corpus: uses out_data corpus
     | uses_inputAlg_computer: uses input_alg computer
     | uses_alphAlg_computer: uses alph_alg computer
     | uses_outAlg_computer: uses out_alg computer
     | uses_inputAlg_corpus: uses input_alg corpus
     | uses_circAlg_corpus: uses circ_alg corpus
     | uses_alphAlg_corpus: uses alph_alg corpus
     | uses_outAlg_corpus: uses out_alg corpus
     | uses_circAlg_user: uses circ_alg user
     | uses_alphAlg_user: uses alph_alg user
     | uses_master_user: uses circ_alg user
     | uses_circDS_inputDS: uses circ_data input_data
     | uses_alphDS_inputDS: uses alph_data input_data
     | uses_alphDS_circDS: uses alph_data circ_data
     | uses_inputDS_circDS: uses input_data circ_data
     | uses_inputDS_alphDS: uses input_data alph_data
     | uses_circDS_alphDS: uses circ_data alph_data.

Inductive satisfies: kwicParameter -> kwicParameter -> Prop :=
    | satisfies_inputAlg_inputType: satisfies input_alg input_type
    | satisfies_circAlg_circType: satisfies circ_alg circ_type
    | satisfies_alphAlg_alphType: satisfies alph_alg alph_type
    | satisfies_outAlg_outType: satisfies out_alg out_type.

Inductive encapsulates: kwicParameter -> kwicParameter -> Prop :=
    | encapsulates_inputType_inputAlg: encapsulates input_type input_alg
    | encapsulates_circType_circAlg: encapsulates circ_type circ_alg
    | encapsulates_alphType_alphAlg: encapsulates alph_type alph_alg
    | encapsulates_outType_outAlg: encapsulates out_type out_alg.

Definition functional_decomposition_dependency := {|
    Uses:= uses;
    Satisfies:= satisfies;
    Encapsulates:= encapsulates
|}.

Example pae_example: providers_always_encapsulate  kwicParameter functional_decomposition_dependency.
Proof.
eapply yes.
constructor.
constructor.
Qed.

