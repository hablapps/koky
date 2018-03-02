Require Import MonadState.
Require Import Id.

Record indexedStateT S1 S2 (m : Type -> Type) Out := mkIndexedStateT
{ runIndexedStateT : S1 -> m (Out * S2)%type }.
Arguments mkIndexedStateT [S1 S2 m Out].
Arguments runIndexedStateT [S1 S2 m Out].

Definition indexedState S1 S2 Out := indexedStateT S1 S2 Id Out.

Definition stateT S m Out := indexedStateT S S m Out.

Definition state S Out := stateT S Id Out.
