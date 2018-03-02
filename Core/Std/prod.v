Require Import Functor.

Instance Functor_prod {A} : Functor (prod A) :=
{ fmap _ _ f pair := (fst pair, f (snd pair)) }.

Instance FunctorDec_prod {A} : FunctorDec (prod A).
Proof.
  split; intros; try destruct fa; auto.
Qed.

Instance Functor_prod' {B} : Functor (fun A => prod A B) :=
{ fmap _ _ f pair := (f (fst pair), (snd pair)) }.

Instance FunctorDec_prod' {B} : FunctorDec (fun A => prod A B).
Proof.
  split; intros; try destruct fa; auto.
Qed.
