Require Import Monad.

Definition Id (A : Type) : Type := A.

Instance Functor_Id : Functor Id :=
{ fmap _ _ f a := f a }.

Instance FunctorDec_Id : FunctorDec Id.
Proof. split; auto. Qed.

Instance Monad_Id : Monad Id :=
{ ret _ x := x
; bind _ _ a f := f a
}.

Instance MonadDec_Id : MonadDec Id.
Proof. split; auto. Qed.
