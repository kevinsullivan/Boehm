import SystemModel.System

/-
An [Assertion] represents a property of system instance states.
-/

definition Assertion {sys_type : SystemType}:= @SystemInstance sys_type -> Prop

/-
An [Action] represents a function that transforms on system 
instance state to another. Currently we don't have a way to
represent additional parameters of such operations.
-/

definition Action {sys_type : SystemType}:= @SystemInstance sys_type -> @SystemInstance sys_type

/-
An [ActionSpec] represents a relation between system instance
states. We use these objects to represent specifications that
Actions must satisfy.
-/
definition ActionSpec {sys_type : SystemType}:= @SystemInstance sys_type -> @SystemInstance sys_type -> Prop


/-
[ChangeSpec] is currently unused. It's here on a possible path to 
a common signature/type for all Ross-style change specifications.
-/

definition ChangeSpec {sys_type : SystemType} := (@Assertion sys_type) -> (sys_type^.Stakeholders) -> @SystemInstance sys_type -> @SystemInstance sys_type -> Prop

definition ActionSatisfiesActionSpec {sys_type : SystemType} (act_spec: ActionSpec) (act: Action): Prop := 
  forall s: @SystemInstance sys_type, 
    act_spec s (act s)

/-
[Changeable] is the leaf node in our Boehm-style means-ends hierarchy.
A proof of a [Changeable] proposition requires a proof, for all contexts,
phases, and stakeholders, of whatever proposition, parameterized by those
values, the user of this overall framework plugs in. 
-/

inductive Changeable (sys_type: SystemType): Prop
| intro : (exists changeable: sys_type ^.Contexts -> sys_type ^.Phases -> sys_type ^.Stakeholders -> @SystemInstance sys_type -> Prop, 
             forall c: sys_type ^.Contexts, forall p: sys_type ^.Phases, 
             forall s: sys_type ^.Stakeholders, forall st: @SystemInstance sys_type, changeable c p s st) ->
          Changeable

