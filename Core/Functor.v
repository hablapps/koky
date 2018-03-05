Require Import Program.Basics.

Open Scope program_scope.

(* typeclass and laws *)

Class Functor (f : Type -> Type) :=
{ fmap {A B} (g : A -> B) : f A -> f B }.

Class FunctorDec f `{Functor f} :=
{ functor_id : forall A (fa : f A), fmap id fa = fa
; functor_comp : 
    forall A B C (h : A -> B) (g : B -> C) (fa : f A),
      (fmap g ∘ fmap h) fa = fmap (g ∘ h) fa
}.

(* theorems *)

Lemma fmap_eq : forall {A B m} (f g : A -> B) (ma : m A) `{Functor m},
  f = g -> fmap f ma = fmap g ma.
Proof.
  intros.
  now rewrite H0.
Qed.
