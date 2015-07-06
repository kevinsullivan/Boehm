
Section Dependency.
  Variable params : Set.
  
  Set Printing Projections.

  Record Dependency : Type := mk_dep {
    Uses : params -> params -> Prop;
    Satisfies : params -> params -> Prop;
    Encapsulates : params -> params -> Prop
  }.

  Inductive depends_on (dep: Dependency) : params -> params -> Prop :=
  | dep_by_use : forall a b, dep.(Uses) a b -> depends_on dep a b
  | dep_by_trans : forall a b c, depends_on dep a b -> depends_on dep b c -> depends_on dep a c.
  
  Definition has_circular_deps (dep : Dependency): Prop :=
    exists a b, depends_on dep a b /\ depends_on dep b a.
  
  Definition bad_circle (dep : Dependency): Prop :=
    exists a b, dep.(Uses) a b /\ dep.(Satisfies) a b.
  
  Inductive providers_always_encapsulate: Dependency -> Prop :=
    yes: forall dep a b, dep.(Satisfies) a b -> dep.(Encapsulates) b a -> providers_always_encapsulate dep .
  
  Definition modular (dep : Dependency): Prop :=
    ~ bad_circle dep /\ providers_always_encapsulate dep /\ ~ has_circular_deps dep.

  Unset Printing Projections.

End Dependency.
