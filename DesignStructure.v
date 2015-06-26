(*
Things to model:
- parameter
- dependence
- design rules (interfaces)
- design decisions

*)
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export Coq.Bool.Bool.

Open Scope string_scope.

(****************************Proposal One*********************************)

(**
System parameter types. Each has one constructor that takes a string (i.e., name of that parameter) and returns a type.
*)

Inductive designParameter := DP: string -> designParameter.

Inductive environmentParameter := EP: string -> environmentParameter.

Inductive designRule := DR: string -> designRule.

(**
System parameters are consisted of design parameters, environment parameters and design rules.
*)
Record systemParameter: Set := mk_sys_parameter 
{
  systemParameter_ep: list environmentParameter;
  systemParameter_dr: list designRule;
  systemParameter_dp: list designParameter
}.

(**
A design structure is consisted of system parameters and the dependency relations. Here I use [list (list bool)] to represent the dependency relations.
It's like a 2D array or a m*n matrix, in which a [true] means there is a dependency just like a mark [X] in the DSM, while a [false] means there isn't a dependency. 
*)
Record designStructure: Set := mk_design_structure
{
  designStructure_sp: systemParameter;
  designStructure_dependecy: list (list bool)
}.



(****************************Functions to do the computation*****************************)

(**
How to compute the cost of making changes to a parameter (The cost here is the number of other parameters that will be changed due to this change):
1. Locate the parameter that will change.
2. Compute the number of parameters that directly depend on it using the dependency relations.
3. Compute the number of parameters that indirectly depend on it using the dependency relations.
4. Sum up the cost.
*)

(**Functions used to do the computation *)

(** Useful notations *)
Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..) : list_scope.

(** Determine environmentParameter equality *)
Definition ep_eq_dec:
  forall a b : environmentParameter, { a = b } + { a <> b }.
repeat decide equality.
Defined.

(** Get the index of [environmentParameter] in a list *)
(**
Fixpoint get_index_ep (l: list environmentParameter) (ep: environmentParameter): nat :=
  match l with
    | nil => 0
    | a::l' => if ep_eq_dec a ep then 1 else (get_index_ep l' ep) + 1
  end.
*)

Fixpoint index_p (ep: environmentParameter) (l:list environmentParameter) {struct l} : nat -> Exc nat :=
  match l with
  | nil => fun p => error
  | b :: m => fun p => if (ep_eq_dec ep b) then (value p) else (index_p ep m (S p))
  end.

Fixpoint get_index_ep (ep: environmentParameter) (l:list environmentParameter): nat := 
  match index_p ep l 1 with
    | None => 0
    | Some n => n
  end.

(**
Compute index_p (EP "User") [EP "Computer", EP "Corpus", EP "User"] 1.
Compute get_index_ep (EP "User") [EP "Computer", EP "Corpus", EP "User"].
*)

(** Count how many [true] in a list *)
Fixpoint count_true (l: list bool): nat :=
    match l with
      | [] => 0
      | y :: tl =>
        let n := count_true tl in
          if eqb y true then S n else n
    end.

(** Get the nth element in a list *)
Fixpoint get_nth (A: Type)(n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, [] => default
      | S m, x :: t => get_nth A m t default
    end.

(** Compute the direct cost of making changes to a [environmentParameter]*)
Fixpoint get_cost_ep (ep: environmentParameter) (ds: designStructure) : nat := 
    match ds with
      mk_design_structure (mk_sys_parameter epl _ _) dsl => count_true (get_nth (list bool) ((get_index_ep ep epl)-1) dsl [])
    end.

Fixpoint get_index_b (l: list bool) (b: bool): nat :=
  match l with
    | nil => 0
    | a::l' => if eqb a b then 1 else (get_index_b l' b) + 1
  end.


Fixpoint get_cost_ep_indirect (ep: environmentParameter) (ds: designStructure) : nat := 
    match ds with
      mk_design_structure (mk_sys_parameter epl _ _) dsl => count_true (get_nth (list bool) ((get_index_ep ep epl)-1) dsl []) +
                                                            count_true (get_nth (list bool) ((get_index_b (get_nth (list bool) ((get_index_ep ep epl)-1) dsl []) true)-1) dsl [])
    end.
(****************************Proposal A_decwo*********************************)

(**
Here I define the system parameter and dependency pairs. Each takes a string and a list of bool, representing the name of the parameter and how it is depended upon, respectively.
Each of them is like a column in the DSM. For example, [DPD "X" false:true:false:nil] indicates that the name of the design parameter is [x], and there is one
other parameter that depends on it.
*)
Inductive designParameter_dependency := DPD: string -> list bool -> designParameter_dependency.

Inductive environmentParameter_dependency := EPD: string -> list bool -> environmentParameter_dependency.

Inductive designRule_dependency := DRD: string -> list bool -> designRule_dependency.

(**
A design structure is consisted of lists of these system papameters.
*)
Record designStrucuture2: Set := mk_design_structure2
{
  designStructure_epd: list environmentParameter_dependency;
  designStructure_drd: list designRule_dependency;
  designStructure_dpd: list designParameter_dependency
}.



