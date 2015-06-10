(** * Introduction *)

(**
This specification is our formalization, in 
the computational part of Coq's type theory,
Gallina, of the semantic approach by Ross,
Beesemyer, and Rhodes, SEAri Working Paper
Series WP-2011-2-2, revised December 16, 2012,
entitled, "A Prescriptive Semantic Basis for
System Lifecycle Properties." The work gives
an interesting approach to defining meanings 
for (change-related) ility terms (terms such
as "flexibility" and "evolvability". Rather
than attempt to impose a preferred definition
on the community, the paper postulates what
we see as a language of change requirements
statements, and then classifies statements as
belonging to certain classes ("tipes" in this
specification). This specification makes this
idea precise using the concepts of programming
language syntax and semantics, and in particular
the definition of a "tipe" assignment operator
for sentences in a language described by what
amounts to a context-free language for change
related requirements, following Ross et al.
*)

(** Changeable General Theory *)
Require Export System.

Inductive Changeable_Ross {msys: MetaSystem} (sys: System msys) : Prop :=
  satisfiesChangeableRequirement:
    (exists changeable: System msys -> Prop, changeable sys) -> Changeable_Ross sys.

(** * Import basic types from Coq libraries *)

Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Export Coq.Strings.Ascii.

(** * Represent identifiers and descriptions as strings *)

Open Scope string_scope.
Open Scope char_scope.

Definition description := string.

(** * A context-free grammer for change-related ility statements *)

Inductive perturbation := 
  | perturbation_disturbance: description -> perturbation
  | perturbation_shift: description -> perturbation
  | perturbation_none: description -> perturbation.

Inductive context := 
  | context_circumstantial: description -> context 
  | context_general: description -> context.


Inductive phase := phase_preOps | phase_ops | phase_interLC.

Inductive agent :=
 | agent_internal: description -> agent
 | agent_external: description -> agent
 | agent_none: description -> agent.

Inductive direction := direction_increase | direction_decrease | direction_maintain.

Inductive parameter := 
  | parameter_level: description -> parameter
  | parameter_set: description -> parameter
  | parameter_value : description -> parameter.

Inductive origin :=
  | origin_one: description -> origin
  | origin_few: description -> origin
  | origin_many: description -> origin.

Inductive destination := 
  | destination_one: description -> destination
  | destination_few: description -> destination
  | destination_many: description -> destination.

Inductive aspect := | aspect_form | aspect_function | aspect_operations.

Inductive mechanism := mechanism_description: description -> mechanism.

Inductive abstraction := 
  | abstraction_architecture: description -> abstraction 
  | abstraction_design: description -> abstraction
  | abstraction_system: description -> abstraction.

Inductive unit :=
  | unit_time_microsecond
  | unit_time_millisecond
  | unit_time_second
  | unit_time_minute
  | unit_time_hour
  | unit_time_day
  | unit_time_week
  | unit_time_month
  | unit_money_dollar.

Inductive reaction := 
  | reaction_sooner_than: nat -> unit -> reaction 
  | reaction_later_than: nat -> unit -> reaction
  | reaction_always: nat -> unit -> reaction.

Inductive span := 
  | span_shorter_than: nat -> unit -> span 
  | span_longer_than: nat -> unit -> span 
  | span_same_as: nat -> unit -> span.

Inductive cost := 
  | cost_less_than: nat -> unit -> cost
  | cost_more_than: nat -> unit -> cost 
  | cost_same_as: nat -> unit -> cost.

Inductive benefit := 
  | benefit_more_than: description -> benefit
  | benefit_less_than: description -> benefit
  | benefit_same_as: description -> benefit.

Inductive valuable := 
  | valuable_simple: description -> valuable
  | valuable_compound: description -> reaction -> span -> cost -> benefit -> valuable.

(**
Having defined the parts of a change requirements
statement, we now pull the parts together to specify
the syntax of what we call a [changeStatement].
*)

(*

VERSION 4 START UPDATES: Factor out related fields to new abstractions, 
[impetus] and [effect], and replace the original fields with these new
fields in [changeStatement].
*)

Record change := mk_change {
  change_direction : direction;
  change_parameter : parameter;
  change_origin : origin;
  change_destination : destination;
  change_aspect : aspect
}.


Record changeStatement: Set := mk_changeStatement
{
  changeStatement_perturbation : perturbation;
  changeStatement_context : context;
  changeStatement_phase : phase;
  changeStatement_agent : agent;
  changeStatement_impetus : change;
  changeStatement_mech_mechanism : mechanism;
  changeStatement_effect : change;
  changeStatement_abstraction: abstraction;
  changeStatement_valuable: valuable
}.

(*
VERSION 4 END UPDATES
*)

(** * Semantic domain, of ility type labels *)

Inductive tipe : Set :=
  | evolvability
  | changeability
  | flexibility
  | adaptability
  | versatility
  | functionalVersatility
  | operationalVersatility
  | substitutability
  | scalability
  | modifiability
  | extensibility
  | agility
  | robustness
  | activeRobustness
  | passiveRobustness
  | reactivity
  | valueRobustness
  | valueSurvivability
  | classicalPassiveRobustness
  | survivability.

(** * Semantics: A simple type assignment operator *)

(** The signature of a type checking rule, used below. *)

Definition tipeCheckingRuleType := changeStatement -> bool.

(** 
We now document a type checking rule for each ility type.
In Ross's theory, types are assigned to sentence in the
language based on their grammatical form. The rules here
are meant to capture the informal presentations of the
corresponding rules given in the 2012 version of Ross's
working paper.
 *)

Definition checkEvolvability (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement (perturbation_shift _) (context_general _) phase_interLC  _ (mk_change (direction_increase | direction_decrease) _ _ _ _) _ (mk_change (direction_increase | direction_decrease) _ _ _ _) (abstraction_architecture _) _ => true
    | _  => false
  end.

Definition checkChangeability (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ _ (agent_external _| agent_internal _) (mk_change (direction_increase | direction_decrease) _ _ _ _) _ (mk_change (direction_increase | direction_decrease) _ _ _ _) _ _=> true
    | _  => false
  end.

Definition checkFlexibility (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ _ (agent_external _) (mk_change (direction_increase | direction_decrease) _ _ _ _) _ (mk_change (direction_increase | direction_decrease) _ _ _ _) _ _ => true
    | _  => false
  end.

Definition checkAdaptability (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ _ (agent_internal _) (mk_change (direction_increase | direction_decrease) _ _ _ _) _ (mk_change (direction_increase | direction_decrease) _ _ _ _) _ _=> true
    | _  => false
  end.

Definition checkVersatility (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ phase_ops _ (mk_change (direction_maintain) _ _ (destination_one _) (aspect_operations | aspect_form)) _ (mk_change (direction_increase | direction_decrease) (parameter_set _) _ (destination_few _ | destination_many _) _) _ _ => true
    | _  => false
  end.

Definition checkFunctionalVersatility (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ phase_ops _ (mk_change (direction_maintain) _ _ (destination_one _) (aspect_operations | aspect_form)) _ (mk_change (direction_increase | direction_decrease) (parameter_set _) _ (destination_few _ | destination_many _) aspect_funtion) _ _ => true
    | _  => false
  end.

Definition checkOperationalVersatility (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ phase_ops _ (mk_change (direction_maintain) _ _ (destination_one _) (aspect_operations | aspect_form)) _ (mk_change (direction_increase | direction_decrease) (parameter_set _) _ (destination_few _ | destination_many _) aspect_operations) _ _ => true
    | _  => false
  end.

Definition checkSubstitutability (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ phase_ops _ (mk_change (direction_maintain) _ _ (destination_one _) (aspect_operations | aspect_function)) _ (mk_change (direction_increase | direction_decrease) (parameter_set _) _ (destination_few _ | destination_many _) aspect_form) _ _ => true
    | _  => false
  end.

Definition checkScalability (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ _ _ (mk_change (direction_maintain) _ _ _ _) _ (mk_change (direction_increase | direction_decrease) (parameter_level _) _ _ _) _ _ => true
    | _  => false
  end.

Definition checkModifiability (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ _ _ (mk_change (direction_maintain) _ _ _ _) _ (mk_change (direction_increase | direction_decrease) (parameter_set _) _ _ _) _ _ => true
    | _  => false
  end.

Definition checkExtensibility (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ phase_ops (agent_external _ | agent_internal _ ) (mk_change (direction_maintain) _ _ _ _) _ (mk_change direction_increase (parameter_set _) _ _ _) _ _ => true
    | _  => false
  end.

Definition checkReactivity (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ _ _ (mk_change (direction_increase | direction_decrease) _ _ _ _) _ (mk_change (direction_increase | direction_decrease) _ _ _ _) _ (valuable_compound _ (reaction_sooner_than _ _) _ _ _) => true
    | _  => false
  end.

Definition checkAgility (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement _ _ _ _ (mk_change (direction_increase | direction_decrease) _ _ _ _) _ (mk_change (direction_increase | direction_decrease) _ _ _ _) _(valuable_compound _ _ (span_shorter_than _ _) _ _) => true
    | _  => false
  end.

Definition checkRobustness (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement (perturbation_shift _) _ phase_ops _ (mk_change _ _ _ _ _) _ (mk_change direction_maintain _ _ (destination_few _) _) _ _ => true
    | _  => false
  end.
  
Definition checkActiveRobustness (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement (perturbation_shift _) _ phase_ops _ (mk_change (direction_increase | direction_decrease) _ _ _ _) _ (mk_change direction_maintain _ _ (destination_few _) _) _ _ => true
    | _  => false
  end.
  
Definition checkPassiveRobustness (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement (perturbation_shift _) _ phase_ops _ (mk_change (direction_maintain) _ _ _ _) _ (mk_change direction_maintain _ _ (destination_few _) _) _ _ => true
    | _  => false
  end.
 
Definition checkValueRobustness (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement (perturbation_shift _) _ phase_ops _ (mk_change _ _ _ _ _) _ (mk_change direction_maintain (parameter_value _) _ (destination_few _) _) _ _ => true
    | _  => false
  end.
  
Definition checkValueSurvivability (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement (perturbation_disturbance _) _ phase_ops _ (mk_change _ _ _ _ _) _ (mk_change direction_maintain (parameter_value _) _ (destination_few _) _) _ _ => true
    | _  => false
  end.

Definition checkClassicalPassiveRobustness (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement (perturbation_shift _) _ phase_ops (agent_none _) (mk_change direction_maintain _ _ (destination_few _) _) _ (mk_change direction_maintain (parameter_level _) _ (destination_few _) aspect_form) (abstraction_system _) _ => true
    | _  => false
  end.

Definition checkSurvivability (s: changeStatement) : bool := 
  match s with 
    | mk_changeStatement (perturbation_disturbance _) _ phase_ops _ (mk_change _ _ _ _ _) _ (mk_change direction_maintain _ _ (destination_few _) _) _ _ => true
    | _  => false
  end.

(**
This helper function assigns a type checking rule to each change type *)

Definition tipeCheckingRule (t: tipe) : tipeCheckingRuleType :=
  match t with
    | evolvability => checkEvolvability
    | changeability => checkChangeability
    | flexibility => checkFlexibility
    | adaptability => checkAdaptability
    | versatility => checkVersatility
    | functionalVersatility => checkFunctionalVersatility
    | operationalVersatility => checkOperationalVersatility
    | substitutability => checkSubstitutability
    | scalability => checkScalability
    | modifiability => checkModifiability
    | extensibility => checkExtensibility
    | agility => checkAgility
    | robustness => checkRobustness
    | activeRobustness => checkActiveRobustness
    | passiveRobustness => checkPassiveRobustness
    | reactivity => checkReactivity
    | valueRobustness => checkValueRobustness
    | valueSurvivability => checkValueSurvivability
    | classicalPassiveRobustness => checkClassicalPassiveRobustness
    | survivability => checkSurvivability
  end.

(**
This function takes a list of change type labels and a statement in the
specified language and returns the sublist of the give type labels that
apply to the given statement, based on the rules specified above.
*)

Fixpoint tipeAssignmentFromList (l: list tipe) (s: changeStatement) : list tipe :=
  filter (fun aTipe => (tipeCheckingRule aTipe) s) l.

(**
Here's the input we'll give to this function: a list of all the type labels 
*)

Definition allChangeTipes := (cons evolvability (cons changeability (cons flexibility (cons adaptability (cons versatility (cons functionalVersatility (cons operationalVersatility (cons substitutability (cons scalability (cons modifiability (cons extensibility (cons agility (cons robustness (cons activeRobustness (cons passiveRobustness (cons reactivity (cons valueRobustness (cons valueSurvivability (cons classicalPassiveRobustness (cons survivability nil)))))))))))))))))))).

(** The change ility type assignment operator We partially evaluate the 
type assignment function with the list of all change ility type labels. 
The resulting function just needs a statement in order to compute a list 
of applicable types. This function is the core of this specification, 
and is meant to capture the concept described by Ross et al.
*)

Definition tipeAssignment := tipeAssignmentFromList allChangeTipes.

(** * An example *)

Open Scope string_scope.

(** Here's an example of a change ility statement *)

Definition changeStatement1 : changeStatement := 
  mk_changeStatement 
    (perturbation_shift "some event")
    (context_circumstantial "some circumstantial context")
    phase_preOps 
    (agent_internal "aAgent")
    (mk_change direction_increase (parameter_level "aParameter") (origin_one "anOrginin") (destination_one "aDestination") aspect_function)
    (mechanism_description "some mechanism") 
    (mk_change direction_increase(parameter_level "anotherParameter") (origin_one "anotherOrginin") (destination_one "anotherDestination") aspect_function)
    (abstraction_architecture "anAbstraction")
    (valuable_compound "valuable because of" 
      (reaction_sooner_than 10 unit_time_second)
      (span_shorter_than 1 unit_time_day)
      (cost_less_than 100 unit_money_dollar)
      (benefit_same_as "keep power on")).


(** 
Here's how to compute its change types in Coq. The result: 
changeability, adaptability, agility, and reactivity. 
*)

(*Compute tipeAssignment changeStatement1.*)

(** * Extract Haskell code implementing this specification *)

(*Extraction Language Haskell.
Recursive Extraction tipeAssignment.*)
