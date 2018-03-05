Require Import Program.Basics.
Require Import Core.Monad.

Open Scope program_scope.

(** Catamorphism for [option]. Folds an [option A] into a [B]. *)
Definition option_fold {A B} (some : A -> B) (none : B) (oa : option A) : B :=
  match oa with
  | Some a => some a
  | None => none
  end.

(* typeclass instances *)

Instance Functor_option : Functor option :=
{ fmap _ _ f := option_fold (Some ∘ f) None }.

Instance FunctorDec_option : FunctorDec option.
Proof.
  split; intros; destruct fa; auto.
Qed.

Instance Monad_option : Monad option :=
{ ret _ := Some
; bind _ _ ox f := option_fold f None ox
}.

Instance MonadDec_option : MonadDec option.
Proof.
  split; intros; try destruct ma; auto.
Qed.
