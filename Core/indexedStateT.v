Require Import MonadState.
Require Import Id.
Require Import Std.prod.
Require Import Util.FunExt.

(* datatype and definitions *)

Record indexedStateT S1 S2 (m : Type -> Type) `{Monad m} Out := mkIndexedStateT
{ runIndexedStateT  : S1 -> m (Out * S2)%type
; execIndexedStateT : S1 -> m S2  := fun s1 => fmap snd (runIndexedStateT s1)
; evalIndexedStateT : S1 -> m Out := fun s1 => fmap fst (runIndexedStateT s1)
}.
Arguments mkIndexedStateT [S1 S2 m _ _ _ Out].
Arguments runIndexedStateT [S1 S2 m _ _ _ Out].

Definition indexedState S1 S2 Out := indexedStateT S1 S2 Id Out.
Definition stateT S m `{Monad m} Out := indexedStateT S S m Out.
Definition state S Out := stateT S Id Out.

(* typeclass instances *)

Ltac indexedStateT_reason :=
  match goal with
  | [ |- context [bind _]] => unfold bind
  | [ |- context [execIndexedStateT] ] => unfold execIndexedStateT
  | [ |- context [evalIndexedStateT] ] => unfold evalIndexedStateT
  | [ |- context [Basics.compose] ] => unfold Basics.compose
  | [ |- {| runIndexedStateT := _ |} = {| runIndexedStateT := _ |} ] => apply f_equal
  | [ |- (fun _ => _) = _ ] => apply functional_extensionality; intros
  | [ |- {| runIndexedStateT := _ |} = ?x ] => destruct x as [rs]
  | [ |- context [ let (_, _) := ?rs ?x in _ ] ] => destruct (rs x)
  end; simpl; auto.

Instance Functor_stateT {S m} `{Monad m} : Functor (stateT S m) :=
{ fmap _ _ f sa := mkIndexedStateT (fun s =>
    fmap (fmap f) (runIndexedStateT sa s)) }.

Instance FunctorDec_stateT {S m} `{Monad m} : FunctorDec (stateT S m).
Proof.
  destruct H0.
  unfold Basics.compose in functor_comp.
  split; intros; simpl; repeat indexedStateT_reason.

  - rewrite prod_proj_id.
    auto.

  - now rewrite (functor_comp _ _ _ _ _ _).
Qed.

Instance Monad_stateT {S m} `{Monad m} : Monad (stateT S m) :=
{ ret _ x := mkIndexedStateT (fun s => ret (x, s))
; bind _ _ sa f := mkIndexedStateT (fun s =>
    runIndexedStateT sa s >>= (fun p => runIndexedStateT (f (fst p)) (snd p)))
}.

Instance MonadDec_stateT {S m} `{MonadDec m} : MonadDec (stateT S m).
Proof.
  destruct H0.
  unfold Basics.compose in *.
  destruct H2.
  split; intros; simpl.

  - rewrite (functional_extensionality_with (
      fun s => left_id _ _ _ (fun p : A * S => runIndexedStateT (f (fst p)) (snd p)))).
    simpl.
    repeat indexedStateT_reason.

  - destruct ma.
    apply f_equal.
    apply functional_extensionality.
    intros.
    assert (G : forall X Y (p : X * Y), @ret _ _ _ H1 _ (fst p, snd p) =
                                        @ret _ _ _ H1 _ p).
    { intros. apply f_equal. now rewrite prod_proj. }
    rewrite (functional_extensionality_with (fun p => G _ _ p)).
    now rewrite right_id.

  - repeat indexedStateT_reason.

  - apply f_equal.
    apply functional_extensionality.
    intros.
    now rewrite functor_rel.
Qed.
