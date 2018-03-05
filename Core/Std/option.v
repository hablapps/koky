Require Import Program.Basics.
Require Import Core.Monad.
Require Import Util.FunExt.

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

(* theorems *)

(** If we use [option] constructor to feed [option_fold] we recover the original 
    value *)
Theorem option_fold_id :
  forall A (oa : option A), option_fold Some None oa = id oa.
Proof.
  intros.
  now destruct oa.
Qed.

(** A function being applied after fold is the same as composing the very same 
    function with the original constructors and fold with them.  *)
Theorem option_fold_f :
  forall {A B C} (some : A -> B) (nil : B) (f : B -> C) (oa : option A),
  @option_fold A C (fun a => f (some a)) (f nil) oa = f (option_fold some nil oa).
Proof.
  intros.
  destruct oa; auto.
Qed.
