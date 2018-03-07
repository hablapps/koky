Require Import Lists.List.
Require Import Std.option.
Require Import Std.sum.
Require Import Category.
Require Import Monad.
Require Import Util.FunExt.

Open Scope list_scope.

(** Affine traversal (aka. optional) gets an optional part [A] from the whole 
    [S] and updates the current part with a new version of it [B], to produce
    a new version of the whole [T]. *)
Record pAffine (S T A B : Type) : Type := mkPAffine
{ preview : S -> A + T
; set : S -> B -> T
}.
Arguments mkPAffine [S T A B].
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

Definition affineIdentity {S} : affine S S :=
  mkPAffine inl (fun _ => id).

Lemma affineDec_identity {S} : affineDec (@affineIdentity S).
Proof. split; auto. Qed.

Definition affineCompose {A B C} 
                         (af1 : affine A B) (af2 : affine B C) : affine A C :=
  mkPAffine
    (fun s => sum_fold 
      (fun a => sum_fold inl (fun _ => inr s) (preview af2 a)) 
      (fun _ => inr s)
      (preview af1 s))
    (fun s b' => sum_fold (fun a => set af1 s (set af2 a b')) id (preview af1 s)).

Lemma affineDec_compose :
  forall A B C (af1 : affine A B) (af2 : affine B C),
    affineDec af1 ->
    affineDec af2 ->
    affineDec (affineCompose af1 af2).
Proof.
  split; simpl; intros.
  
  - (* preview_set *)
    destruct H.
    destruct H0.
    admit.

  - (* set_preview *)
    admit.

  - (* set_set *)
    destruct H.
    destruct H0.
    rewrite preview_set0.

    destruct (preview af1 s).
    simpl.

    + rewrite (fun_ext_with (fun _ => set_set0 _ _ _)).
      rewrite sum_fold_f.
      rewrite set_preview0.
      pose proof sum_fold_fg.
      unfold Basics.compose in H.
      rewrite H.
      rewrite set_set1.

    + admit.
    admit.

Admitted.

Instance Category_affine : Category affine :=
{ identity _ := mkPAffine inl (fun _ => id) 
; compose _ _ _ af1 af2 := mkPAffine
    (fun s => sum_fold 
      (fun a => sum_fold inl (fun _ => inr s) (preview af2 a)) 
      inr (preview af1 s))
    (fun s b' => sum_fold (fun a => set af1 s (set af2 a b')) id (preview af1 s))
}.

Instance CategoryDec_affine : CategoryDec affine.
Proof.
  split; simpl; intros.

  - (* left_id *)
    destruct cab.
    unfold id.
    simpl.
    admit.

  - (* right_id *)
    admit.

  - (* assoc *)
    admit.

Admitted.

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
