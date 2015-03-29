(** * Draft Coq Spec derived from Boehm 2015 QA Ontology *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March 23, 2015
*)

(** CONTEXT definition now is imported here as a seprate module.**)
Require Import Context.

(** Stakeholder definition now is imported here as a seprate module.**)
Require Import Stakeholder.

Module MissionEffective.
(** ** SYSTEM PROPERTIES AND RELATIONS *)

(**
We now turn from data types to properties of systems and relations involving them. 
We represent a property as a family of propositions, parameterized by a [System].
We represent a context-dependent "system property" as a binary relation over [System]
and [Context] pairs. We represent a subjective, context-dependent "system property"
as a ternary relation over [System], [Context], [Stakeholder] triples. In all cases, for
purposes of producing a simplest possible example, for each property and relation
we define a proof constructor that in effect axiomatically provides a proof of the given
property or relation for all possible values of [System], [Context], [Stakeholder]. 
*)

(** ** Some basic objective but context-dependent system properties *)

(**
Here we define [PhysicalCapability], [CyberCapability], and other "ilities" as
(objective) properties of specific [Systems] in specific [Contexts]. For each 
property we provide a proof constructor that returns a proof of validity of a
proposition that that property holds "axiomatically" -- for any [System] and 
any [Context]. Any genuinely meaningful use of these techniques would 
require more constrained forms of evidence validate such propositions.
Formally speaking we are defining these "ilities" not as "unary properties" 
(e.g., of [Systems] along) but as "binary relations", in this case relations 
over [System]/[Context] pairs. Here these relations are trivially defined to
hold for all such pairs. In real systems, that might not always be the case,
and even if it were, it would in general be harder to prove! 
*)

Inductive hasRequiredPhysicalCapability: System.System -> Context.Context -> Prop := 
  proofOfPhysicalCapability: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredPhysicalCapability s c.

Inductive hasRequiredCyberCapability: System.System -> Context.Context -> Prop := 
  proofOfCyberCapability: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredCyberCapability s c.

Inductive hasRequiredHumanUsability: System.System -> Context.Context ->  Prop := 
  proofOfHumanUsability: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredHumanUsability s c.

Inductive hasRequiredSpeed: System.System -> Context.Context -> Prop := 
  proofOfSpeed: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredSpeed s c.

Inductive hasRequiredEndurability: System.System -> Context.Context -> Prop := 
  proofOfEndurability: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredEndurability s c.

Inductive hasRequiredManeuverability: System.System -> Context.Context -> Prop := 
  proofOfManeuverability: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredManeuverability s c.

Inductive hasRequiredAccuracy: System.System -> Context.Context -> Prop := 
  proofOfAccuracy: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredAccuracy s c.

Inductive hasRequiredImpact: System.System -> Context.Context -> Prop := 
  proofOfImpact: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredImpact s c.

Inductive hasRequiredScalability: System.System -> Context.Context -> Prop := 
  proofOfScalability: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredScalability s c.

Inductive hasRequiredVersatility: System.System -> Context.Context -> Prop := 
  proofOfVersatility: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredVersatility s c.

Inductive hasRequiredInteroperability: System.System -> Context.Context -> Prop := 
  proofOfInteroperability: forall (s: System.System), forall (c: Context.Context), 
    hasRequiredInteroperability s c.

(**
One potentially important insight that "jumps out" even from this simple 
analysis is that we should not think of "ilities" such as [PhysicalCapability]
as a system properties but as relations over systems and other entities, in
this case, [Contexts].
*)

(** ** Mission-effectiveness as a subjective system property *)

(**
We now formaliz a class of propositions of the form "System s is Mission Effective."
However, we do this in such a way that proof of such a proposition will require a set
of proofs proof that [s] is "subjectively mission effective" from the perspective of each,
and for all [Contexts] in which the system is specified to operate. The "property" of
being mission effective is thus seen to involve, in this formulation, a ternary relation: 
on [Systems], [Contexts], and [Stakeholders]. 

We define the [isMissionEffective] property in three steps:
   - the ternary relation of a system being subjectively effective for a stakeholder in a context
  - the binary relation of being effective (for all stakeholders) in a context
  - the unary property of being effective (for all stakeholders, in all contexts)
*)

(**
This construct defines a ternary relation, an instance of which we interpret as a proposition
that a given [System], [s], in a given [Context], c, is subjectively "mission effective" for a
given [Stakeholder], sh, and that this is provably the case if and only if the required set of
arguments can be provided to the proof constructor, [is_stakeholder_mission_effective]. In
particular, one must provide proofs of all of the constituent propositions, e.g., the system
"has the required physical capability," etc. If the constructor is applied to aguments  of the
required "proof" types, then it will return a proof of stakeholder mission effectiveness for the
given [System] in the given [Context] for the given [Stakeholder].
*)

Inductive Is_stakeholder_effective_in_context (s: System.System) (sh: Stakeholder.Stakeholder s) (c: Context.Context): Prop :=
   is_stakeholder_mission_effective: 
      hasRequiredPhysicalCapability s c -> hasRequiredCyberCapability s c -> 
      hasRequiredHumanUsability s c -> hasRequiredSpeed s c -> hasRequiredEndurability s c -> 
      hasRequiredManeuverability s c -> hasRequiredAccuracy s c -> hasRequiredImpact s c -> 
      hasRequiredScalability s c -> hasRequiredInteroperability s c -> 
          Is_stakeholder_effective_in_context s sh c.

(**
We now express the notion that a [System] is effective in a given [Context], where
constructing a proof that this relation holds requires as input only a proof of the 
proposition that the [System] is subjectively mission effective for all stakeholders
in the given [Context]. 
*)

Inductive MissionEffectiveInContext (s: System.System) (c: Context.Context): Prop := 
  is_mission_eff_in_context: 
    (forall sh: Stakeholder.Stakeholder s, Is_stakeholder_effective_in_context s sh c) -> 
        MissionEffectiveInContext s c.

(**
Finally we can formalize the property of a [System] being mission effective, where a
proof of this property requires as a input a proof that, for all [Contexts], the system is
mission effective (implicitly for all [Stakeholders]) in those [Contexts]. 
*)
Inductive MissionEffective (s: System.System): Prop := 
  mk_mission_eff: 
    (forall c: Context.Context, forall sh: Stakeholder.Stakeholder s, MissionEffectiv