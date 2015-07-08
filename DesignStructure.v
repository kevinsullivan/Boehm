Require Export List String.

Section Dependency.
  Context  {params : Set}.
  
  Set Printing Projections.

  Record Module : Set := mk_module {
   elements: list params;
   name: string
  }.

  Fixpoint inModule (m: Module) (p: params): Prop :=
    In p m.(elements).

  Record Dependency : Type := mk_dep {
    Modules : list Module;
    Volatile : params -> Prop;
    Uses : params -> params -> Prop;
    Satisfies : params -> params -> Prop;
    Encapsulates : params -> params -> Prop
  }.

  Fixpoint inDependency (d: Dependency) (m: Module): Prop :=
    In m d.(Modules).

  (* Theorem : Any "Likely to change" parameter does not leak its volatility to other modules *)
  (* This says nothing about other parameters *)

  Inductive VolatileStar (dep : Dependency) : params -> Prop :=
    | VRefl : forall p, dep.(Volatile) p -> VolatileStar dep p
    | VUse : forall a b, VolatileStar dep b
                      -> dep.(Uses) a b
                      -> VolatileStar dep a
    | VSatisfies : forall a b, VolatileStar dep b
                          -> dep.(Satisfies) a b
                          -> VolatileStar dep a.

  Definition separate_modules (dep : Dependency) (a b: params): Prop :=
    forall m1 m2, inDependency dep m1 -> inDependency dep m2
             -> inModule m1 a
             -> inModule m2 b
             -> m1 <> m2.

  (* Good *)
  Definition hides_volatility (dep: Dependency): Prop :=
    forall a b, dep.(Satisfies) a b \/ dep.(Uses) a b
           -> VolatileStar dep b
           -> exists m, (inModule m a /\ inModule m b).

  (* Good *)
  Definition no_cross_module_circular_use (dep : Dependency): Prop :=
    forall a b, dep.(Uses) a b ->
           dep.(Uses) b a ->
           ~ separate_modules dep a b.

  (* Good *)
  Definition no_circular_satisfaction (dep : Dependency): Prop :=
    forall a b, dep.(Satisfies) a b ->
           ~ dep.(Satisfies) b a.

  (* Good *)
  Definition satisfy_and_encapsulate_coupled (dep : Dependency): Prop :=
    forall a b, dep.(Satisfies) a b -> dep.(Encapsulates) b a.


  (* Good *)
  Definition modular (dep : Dependency): Prop :=
    no_circular_satisfaction dep
    /\ satisfy_and_encapsulate_coupled dep
    /\ hides_volatility dep.

  Lemma separate_commute : forall d a b, separate_modules d a b -> separate_modules d b a.
  Proof.
    unfold separate_modules.
    eauto.
  Qed.      

  Unset Printing Projections.

End Dependency.
