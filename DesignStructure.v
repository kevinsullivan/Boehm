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
    Uses : params -> params -> Prop;
    Satisfies : params -> params -> Prop;
    Encapsulates : params -> params -> Prop
  }.

  Inductive depends_on (dep: Dependency) : params -> params -> Prop :=
  | dep_by_use : forall a b, dep.(Uses) a b -> depends_on dep a b
  | dep_by_trans : forall a b c, depends_on dep a b -> depends_on dep b c -> depends_on dep a c.

  Inductive share_module (dep : Dependency) : params -> params -> Prop :=
    | share : forall m a b, In m dep.(Modules)
                       -> inModule m a
                       -> inModule m b
                       -> share_module dep a b.
  
  Definition has_circular_deps (dep : Dependency): Prop :=
    exists a b, depends_on dep a b /\ depends_on dep b a /\ ~ share_module dep a b.
  
  Definition cross_module_circularity (dep : Dependency): Prop :=
    exists a b, (depends_on dep a b /\
            depends_on dep b a /\
            ~ share_module dep a b).

  Definition use_and_satisfy (dep : Dependency): Prop :=
    exists a b, dep.(Uses) a b /\ dep.(Satisfies) a b.

  Lemma share_commute : forall d a b, share_module d a b -> share_module d b a.
    Proof.
      intros.
      inversion H; subst; clear H.
      econstructor; eauto.
    Qed.      

    Hint Rewrite share_commute.
  
  Inductive providers_always_encapsulate: Dependency -> Prop :=
    yes: forall dep a b, dep.(Satisfies) a b -> dep.(Encapsulates) b a -> providers_always_encapsulate dep .
  
  Definition modular (dep : Dependency): Prop :=
    ~ cross_module_circularity dep /\
    ~ use_and_satisfy dep /\
    providers_always_encapsulate dep /\
    ~ has_circular_deps dep.

  Unset Printing Projections.

End Dependency.
