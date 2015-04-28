(** ** SYSTEM MODULE**)

(**
Kevin Sullivan, Chong Tang, Ke Dou, with Donna Rhodes, 
Barry Boehm, and Adam Ross 

March, 2015
*)

Module System.
(** 
We can't concretely specify non-functional properties absent a model of the system.
We introduce a data type of system models, currently "stubbed out" as having only
one system model, [aSystem], without any further elaboration.
*)
  Inductive System := aSystem.

End System.
