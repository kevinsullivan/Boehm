Require Export System.

Section Changeable.

(**
[sys_type: SystemType] is an implicit parameter of definitions in this section.
*)

Context {sys_type : SystemType}.

(**
An [Assertion] represents a property of system instance states.
*)

Definition Assertion := @SystemInstance sys_type -> Prop.

(** 
An [Action] represents a function that transforms on system 
instance state to another. Currently we don't have a way to
represent additional parameters of such operations.
*)

Definition Action := @SystemInstance sys_type -> @SystemInstance sys_type.

(**
An [ActionSpec] represents a relation between system instance
states. We use these objects to represent specifications that
Actions must satisfy.
*)
Definition ActionSpec := @SystemInstance sys_type -> @SystemInstance sys_type -> Prop.


(**
[ChangeSpec] is currently unused. It's here on a possible path to 
a common signature/type for all Ross-style change specifications.
*)

Definition ChangeSpec := Assertion -> Stakeholders sys_type -> @SystemInstance sys_type -> @SystemInstance sys_type -> Prop.

(**
[ActionSatisfiesActionSpec] returns a proposition stating that an 
action satisfies a given specification.
*)

Definition ActionSatisfiesActionSpec (act_spec: ActionSpec) (act: Action): Prop := 
  forall s: @SystemInstance sys_type, 
    act_spec s (act s).

Hint Unfold ActionSatisfiesActionSpec.
(**
[Changeable] is the leaf node in our Boehm-style means-ends hierarchy.
A proof of a [Changeable] proposition requires a proof, for all contexts,
phases, and stakeholders, of whatever proposition, parameterized by those
values, the user of this overall framework plugs in. 
*)

Inductive Changeable (sys_type: SystemType): Prop :=
  satisfiesChangeabilityRequirements:
    (exists changeable: Contexts sys_type -> Phases sys_type -> Stakeholders sys_type -> @SystemInstance sys_type -> Prop, 
      forall c: Contexts sys_type, forall p: Phases sys_type, forall s: Stakeholders sys_type, forall st: @SystemInstance sys_type, changeable c p s st) ->
        Changeable sys_type.

Hint Constructors Changeable.

End Changeable.
