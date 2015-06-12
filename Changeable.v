(**
"<who> needs to be able to change <what> <when> <why>"
*)
Require Export System.

Section Changeable.


  Context {msys : MetaSystem}.

  (** Convenience Aliasing *)
  Definition stakeholders := (stakeholders msys).
  Definition resources := (resources msys).
  Definition phases := (phases msys).
  Definition contexts := (contexts msys).
  Definition system_type := (system_type msys).
  
  (** TODO: Some sort of quantifying value in Cost and Benefit? *)
  Inductive Cost := 
    | cost_simple: resources -> Cost.

  Inductive Benefit :=
    | benefit_simple: resources -> Benefit.

  Definition get_cost (c: Cost): resources :=
    match c with
        | cost_simple r => r
    end.
  
  Definition get_benefit (b: Benefit): resources :=
    match b with
        | benefit_simple r => r
    end.

  Record Value := mk_value {
    cost: Cost;
    benefit: Benefit 
  }.

  (** Note: Hoare logic over system_type could evolve to a Hoare logic over values of Metasystem type [msys] *)
  Definition Assertion := msys -> Prop.

  Definition Action := msys -> msys.

  Record Change := mk_change {
    changePrecondition: Assertion;
    changeAction: Action;
    changePostcondition: Assertion
  }.

  Record ChangeRequirement : Type := mkChangeRequirement {
    trigger: Assertion;
    sh: stakeholders;
    ctxt: contexts;
    ph: phases;
    change: Change;
    value: Value -> Prop
  }.

  Inductive Changeable (sys: System msys) : Prop :=
    satisfiesChangeabilityRequirement:
      (exists changeable: System msys -> Prop, changeable sys) ->
      Changeable sys.

End Changeable.
