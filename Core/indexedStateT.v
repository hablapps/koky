Require Import MonadState.
Require Import Id.
Require Import Std.prod.

Record indexedStateT S1 S2 (m : Type -> Type) Out := mkIndexedStateT
{ runIndexedStateT : S1 -> m (Out * S2)%type }.
Arguments mkIndexedStateT [S1 S2 m Out].
Arguments runIndexedStateT [S1 S2 m Out].

Definition indexedState S1 S2 Out := indexedStateT S1 S2 Id Out.

Definition stateT S m Out := indexedStateT S S m Out.

Definition state S Out := stateT S Id Out.

Instance Functor_stateT {S m} `{Monad m} : Functor (stateT S m) :=
{ fmap _ _ f sa := mkIndexedStateT (fun s =>
    fmap (fmap f) (runIndexedStateT sa s)) }.

Instance FunctorDec_stateT {S m} `{Monad m} : FunctorDec (stateT S m).
Admitted.

Instance Monad_stateT {S m} `{Monad m} : Monad (stateT S m).
Admitted.

Instance MonadDec_stateT {S m} `{Monad m} : MonadDec (stateT S m).
Admitted.