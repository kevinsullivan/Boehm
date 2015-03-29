(** * Draft Coq Spec derived from Boehm 2015 QA Ontology *)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

(** System definition now is imported here as a seprate module.**)
Require Import System.

(** CONTEXT definition now is imported here as a seprate module.**)
Require Import Context.

(** ** FLEXIBILITY**)
(**
We first define the basic context-dependent system attributes for [Flexibility].
*)
Inductive Modifiability: System.System -> Context.Context -> Prop := 
  proofOfModifiability: forall (s: System.System), forall (c: Context.Context), Modifiability s c.

Inductive Tailorability: System.System -> Context.Context -> Prop := 
  proofOfTailorability: forall (s: System.System), forall (c: Context.Context), Tailorability s c.

Inductive Adaptability: System.System -> Context.Context -> Prop := 
  proofOfAdaptability: forall (s: System.System), forall (c: Context.Context), Adaptability s c.

(**
As we did before, we define [aSystem is Flexible] in two steps:
  - a system is flexible in a context.
  - a system is universally flexible.
*)
Inductive Flexible_In_Context (s: System.System) (c: Context.Context) : Prop :=
    is_flexible_in_context: Modifiability s c -> Tailorability s c -> 
        Adaptability s c -> Flexible_In_Context s c.

Inductive Flexible (s: System.System) : Prop :=
