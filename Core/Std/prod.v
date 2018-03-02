Require Import FunctionalExtensionality.
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

Lemma prod_proj :
  forall A B (pr : A * B), pr = (fst pr, snd pr).
Proof.
  now destruct pr.
Qed.

Lemma prod_proj_id : 
  forall A B, (fun pr : A * B => (fst pr, snd pr)) = id.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  now rewrite prod_proj.
Qed.
