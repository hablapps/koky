Require Import Program.Basics.
Require Import Functor.
Require Export Functor.

Class Monad m `{FunctorDec m} : Type :=
{ ret  : forall {X}, X -> m X
; bind : forall {A B}, m A -> (A -> m B) -> m B
}.
Notation "ma >>= f" := (bind ma f) (at level 50, left associativity).
Notation "ma >> mb" := (ma >>= fun _ => mb) (at level 50, left associativity).

Class MonadDec m `{Monad m} :=
{ left_id : forall {A B} (a : A) (f : A -> m B), ret a >>= f = f a
; right_id : forall {A} (ma : m A), ma >>= ret = ma
; assoc : 
    forall {A B C} (ma : m A) (f : A -> m B) (g : B -> m C),
      ma >>= f >>= g = ma >>= (fun x => f x >>= g)
; functor_rel : forall {A B} (ma : m A) (f : A -> B), fmap f ma = ma >>= ret ∘ f
}.
