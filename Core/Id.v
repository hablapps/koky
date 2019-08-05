Require Import Monad.

Definition Id (A : Type) : Type := A.

Instance Functor_Id : Functor Id :=
{ fmap A B f a := f a }.

Instance FunctorDec_Id : FunctorDec Id.
Proof. split; auto. Qed.

Instance Monad_Id : Monad Id :=
{ ret A x := x
; bind A B a f := f a
}.

Instance MonadDec_Id : MonadDec Id.
Proof. split; auto. Qed.
