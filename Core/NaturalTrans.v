Require Import Functor.

Record naturalTrans f g `{Functor f, Functor g} := mkNaturalTrans
{ runNaturalTrans : forall X, f X -> g X }.
Notation "f ~> g" := (naturalTrans f g) (at level 50, left associativity).
Arguments mkNaturalTrans [f g _ _].
Arguments runNaturalTrans [f g _ _] _ [X].

Record naturalTransDec f g `{Functor f, Functor g} (φ : f ~> g) :=
{ naturalTrans_comm : 
    forall A B (fa : f A) (g : A -> B),
      runNaturalTrans φ (fmap g fa) = fmap g (runNaturalTrans φ fa)
}.

Definition composeNaturalTrans {f g h : Type -> Type} 
                              `{Functor f, Functor g, Functor h}
                               (nt1 : g ~> h) (nt2 : f ~> g) : f ~> h :=
  mkNaturalTrans (fun _ fx => runNaturalTrans nt1 (runNaturalTrans nt2 fx)).
Notation "f • g" := (composeNaturalTrans f g) (at level 40, left associativity).
