Require Import Lists.List.
Require Import Std.option.
Require Import Std.sum.

Open Scope list_scope.

(** Affine traversal (aka. optional) gets an optional part [A] from the whole 
    [S] and updates the current part with a new version of it [B], to produce
    a new version of the whole [T]. *)
Record pAffine (S T A B : Type) : Type := mkAffine
{ preview : S -> A + T
; set : S -> B -> T
}.
Arguments mkAffine [S T A B].
Arguments preview [S T A B].
Arguments set [S T A B].

(** Monomorphic affine *)
Definition affine S A : Type := pAffine S S A A.

Record affineDec {S A} (af : affine S A) :=
{ preview_set : forall s, sum_fold (set af s) id (preview af s) = s
; set_preview : forall s a, 
                   preview af (set af s a) = 
                   sum_fold (fun _ => inl a) inr (preview af s)
; set_set : forall s a1 a2, set af (set af s a1) a2 = set af s a2
}.

(** Provides access to the head of a list. *)
Definition head {A} : affine (list A) A :=
  mkAffine (fun s => option_fold inl (inr nil) (hd_error s)) (fun s a' =>
    match s with
    | _ :: t => a' :: t
    | Nil => Nil
    end).

Definition headDec {A} : affineDec (@head A).
Proof.
  split; intros s; destruct s; auto.
Qed.
