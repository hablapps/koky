Require Import Program.Basics.
Require Import Monad.
Require Export Functor.
Require Export Monad.

Open Scope program_scope.

Class MonadState (A : Type) (m : Type -> Type) `{MonadDec m} :=
{ get : m A
; put : A -> m unit
; modify : (A -> A) -> m unit := fun f => get >>= (put ∘ f)
}.

Class MonadStateDec (A : Type) (m : Type -> Type) `{MonadState A m} :=
{ get_get : get >>= (fun s1 => get >>= (fun s2 => ret (s1, s2))) =
            get >>= (fun s => ret (s, s))
; get_put : get >>= put = ret tt
; put_get : forall s, put s >> get = put s >> ret s
; put_put : forall s1 s2, put s1 >> put s2 = put s2
}.
