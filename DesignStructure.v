Require Export System.
Require Export Changeable.

(** ** Context *)

Inductive KWICContexts := nominal.

(** ** Phase *)

(**
[KWICPhases] represents the lifecycle phases of a software system.
*)

(** design, implementation and maintenance are talked about in the paper*)
Inductive KWICPhases := requirements | design | implementation | testing | deployment | maintenance.

(** ** Stakeholder *)

(**
[KWICStakeholders] represents the set of potential system change agents
*)

Inductive KWICStakeholders :=  developer | customer.

(** Dependency Relation Class*)
Class Dependency (SystemParameter: Set) (Stakeholder: Set):= {
    (* Relation between system parameters and stakeholders​, to make sure if a system parameter is an environment parameter. *)
    isEP: SystemParameter -> Stakeholder -> Prop;
    (* Relation among environment parameters: affect *)
    affect: SystemParameter -> SystemParameter -> Prop;
    (* Relation between interfaces and environment parameters: adapt *)
    adapt: SystemParameter -> SystemParameter -> Prop;
    (* Relation between data structure and environment parameters: ds_ep *)
    ds_ep: SystemParameter -> SystemParameter -> Prop;
    (* Relation between algorithm and environment parameters: alg_ep *)
    alg_ep: SystemParameter -> SystemParameter -> Prop;
    (* Relation between master and environment parameters: ms_ep *)
    ms_ep: SystemParameter -> SystemParameter -> Prop;
    (* Relation between data structures and interfaces: satisfy *)
    satisfy: SystemParameter -> SystemParameter -> Prop;
    (* Relation between algorithms and interfaces: implement *)
    implement: SystemParameter -> SystemParameter -> Prop;
    (* Relation among interfaces: call *)
    call: SystemParameter -> SystemParameter -> Prop;
    (* Relation between algorithms and data structures: access *)
    access: SystemParameter -> SystemParameter -> Prop;
    (* Relation among data structures: rely *)
    rely: SystemParameter -> SystemParameter -> Prop;
    (* Relation between master and interfaces: control *)
    control: SystemParameter -> SystemParameter -> Prop;
    (* Higher order relation: dependOn. It should be a combination of the above relations, and it holds if any of the above relations holds *)
    dependOn: SystemParameter -> SystemParameter -> Prop;
    (* Transitive dependency relation *)
    dependOn_trans: forall x y z: SystemParameter, dependOn x y -> dependOn y z -> dependOn x z
}.