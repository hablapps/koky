Require Import Program.Basics.
Require Import Monad.
Require Export Functor.
Require Export Monad.
Require Import Util.FunExt.

Open Scope program_scope.

(* typeclass and laws *)

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

(* theorems *)

Lemma general_getget :
  forall {m : Type -> Type} {A : Type} `{MonadStateDec A m} 
         {X : Type} (p : A * A -> m X),
    get >>= (fun x1 => get >>= (fun x2 => p (x1, x2))) =
    get >>= (fun x1 => p (x1, x1)).
Proof.
  intros.
  destruct H2.
  destruct H4.
  rewrite (functional_extensionality_with' (fun x1 => left_id _ _ (x1, x1) p)).
  rewrite <- (assoc _ _ _ _ _ _).
  rewrite <- get_get0.
  rewrite -> (assoc _ _ _ _ _ _).
  unwrap_layer.
  rewrite -> (assoc _ _ _ _ _ _).
  unwrap_layer.
  now rewrite left_id.
Qed.

Lemma non_eff_get :
  forall  {m A} `{MonadStateDec A m} {X : Type} (p : m X),
    get >> p = p.
Proof.
  intros.
  pose proof (@general_getget m A _ _ _ _ _ _).
  destruct H2.
  destruct H4.
  rewrite <- (left_id _ _ tt (fun _ => p)).
  rewrite <- get_put0.
  rewrite (assoc _ _ _ _ _ _).
  now rewrite (H5 _ (fun pr => put (snd pr) >> p)).
Qed.
