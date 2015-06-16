(**
"<who> needs to be able to change <what> <when> <why>"
*)
Require Export System.

Section Changeable.


  Context {sys : System}.

  (** Convenience Aliasing *)
  Definition context := (Contexts sys).
  Definition stakeholder := (Stakeholders sys).
  Definition phase := (Phases sys).
  Definition artifact := (Artifacts sys).
  Definition value := (Value sys).

  (** Note: Hoare logic over artifacts could evolve to a Hoare logic over values of System type [sys] *)
  Definition Assertion := System -> Prop.

  Definition Action := System -> System.

  Record Change := mk_change {
    changePrecondition: Assertion;
    changeAction: Action;
    changePostcondition: Assertion
  }.

  Record ChangeRequirement : Type := mkChangeRequirement {
    trigger: Assertion;
    sh: stakeholder;
    ctxt: context;
    ph: phase;
    change: Change;
    val:= value -> Prop
  }.

  Inductive Changeable (sys: System) : Prop :=
    satisfiesChangeabilityRequirement:
      (exists changable: context -> stakeholder -> phase -> artifact -> value -> Prop, 
       exists af: artifact,
       exists val: value,
       (forall ctxt: context, forall sh: stakeholder, forall ph: phase, changable ctxt sh ph af val)) ->
    Changeable sys.

End Changeable.
