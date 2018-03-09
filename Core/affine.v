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
Record pAffine (S T A B : Type) := mkPAffine
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

(** Alternative affine representation, easier for proving. *)
Record affine' S A := mkAffine'
{ preview' : S -> option A
; set' : S -> A -> S
}.
Arguments mkAffine' [S A].
Arguments preview' [S A].
Arguments set' [S A].

Record affine'Dec {S A} (af : affine' S A) :=
{ preview'_set' : forall s, option_fold (set' af s) s (preview' af s) = s
; set'_preview' : forall s a,
                    preview' af (set' af s a) =
                    fmap (fun _ => a) (preview' af s)
; set'_set' : forall s a1 a2, set' af (set' af s a1) a2 = set' af s a2
}.

Definition affine'Identity {S} : affine' S S :=
  mkAffine' Some (fun _ => id).

Lemma affine'Dec_identity {S} : affine'Dec (@affine'Identity S).
Proof. split; auto. Qed.

Definition affine'Compose {A B C} 
                         (af1 : affine' A B) (af2 : affine' B C) : affine' A C :=
  mkAffine'
    (fun a => preview' af1 a >>= preview' af2)
    (fun a c' => option_fold 
      (fun b => set' af1 a (set' af2 b c')) a (preview' af1 a)).

Definition affine'Compose' {A B C} 
                         (af1 : affine' A B) (af2 : affine' B C) : affine' A C :=
  mkAffine'
    (fun a => preview' af1 a >>= preview' af2)
    (fun a c' => option_fold 
      (fun b => set' af1 a (option_fold 
        (fun _ => set' af2 b c') b (preview' af2 b))) 
      a (preview' af1 a)).

Lemma affine'Dec_compose' :
  forall A B C (af1 : affine' A B) (af2 : affine' B C),
    affine'Dec af1 ->
    affine'Dec af2 ->
    affine'Dec (affine'Compose' af1 af2).
Proof.
  intros.
  destruct H.
  destruct H0.
  split; simpl; intros.

  - (* preview'_set' *)
    rewrite option_fold_bis.
    assert (H :
      option_fold
        (fun y : B =>
         option_fold
           (fun c' : C =>
            option_fold
              (fun b : B => set' af1 s (option_fold (fun _ : C => set' af2 b c') b (preview' af2 b))) s
              (preview' af1 s)) s (preview' af2 y)) s (preview' af1 s) =
      option_fold
        (fun y : B =>
         option_fold
           (fun c' : C =>
            option_fold
              (fun b : B => set' af1 s (option_fold (set' af2 b) b (preview' af2 b))) s
              (preview' af1 s)) s (preview' af2 y)) s (preview' af1 s)).
    { destruct (preview' af1 s); simpl; auto.
      destruct (preview' af2 b); simpl; auto.
    }
    rewrite H.
    clear H.
    rewrite (fun_ext_with_nested (set' af1 s) (fun _ => preview'_set'1 _)).
    rewrite (fun_ext_with (fun _ => preview'_set'0 _)).
    unfold option_fold.
    destruct (preview' af1 s); simpl; auto.
    destruct (preview' af2 b); simpl; auto.

  - (* set'_preview' *)
    simpl in *.
    unfold Basics.compose in *.
    rewrite <- (option_fold_f _ _ (preview' af1) _).
    rewrite (fun_ext_with (fun _ => set'_preview'0 _ _)).
    assert (H :
      option_fold (preview' af2) None
        (option_fold
           (fun s0 : B =>
            option_fold
              (fun _ : B =>
               Some (option_fold (fun _ : C => set' af2 s0 a) s0 (preview' af2 s0)))
              None (preview' af1 s)) (preview' af1 s) (preview' af1 s)) =
      option_fold (preview' af2) None
        (option_fold
           (fun s0 : B => Some (option_fold (fun _ : C => set' af2 s0 a) s0 (preview' af2 s0))) 
           None 
          (preview' af1 s))).
    { destruct (preview' af1 s); simpl; auto. }
    rewrite H; clear H.
    rewrite <- (option_fold_f _ _ (option_fold (preview' af2) None) _).
    assert (H :
      option_fold
        (fun a0 : B =>
         option_fold (preview' af2) None
           (Some (option_fold (fun _ : C => set' af2 a0 a) a0 (preview' af2 a0))))
        (option_fold (preview' af2) None None) (preview' af1 s) =
      option_fold
        (fun a0 : B => 
           preview' af2 (option_fold (fun _ : C => set' af2 a0 a) a0 (preview' af2 a0)))
        None
        (preview' af1 s)).
    { destruct (preview' af1 s); simpl; auto. }
    rewrite H; clear H.
    rewrite (fun_ext_with' (fun _ => option_fold_f _ _ (preview' af2) _)).
    assert (H :
      option_fold
        (fun s0 : B =>
         option_fold (fun _ : C => preview' af2 (set' af2 s0 a)) 
           (preview' af2 s0) (preview' af2 s0)) None (preview' af1 s) =
      option_fold
        (fun s0 : B =>
         option_fold (fun _ : C => option_fold (fun _ : C => Some a) None (preview' af2 s0)) 
           (preview' af2 s0) (preview' af2 s0)) None (preview' af1 s)).
    { destruct (preview' af1 s); simpl; auto.
      now rewrite (fun_ext_with (fun _ => set'_preview'1 _ _)). }
    rewrite H; clear H.
    destruct (preview' af1 s); simpl; auto.
    destruct (preview' af2 b); simpl; auto.

  - (* set'_set' *)
    admit.

Admitted.

Lemma affine'Dec_compose :
  forall A B C (af1 : affine' A B) (af2 : affine' B C),
    affine'Dec af1 ->
    affine'Dec af2 ->
    affine'Dec (affine'Compose af1 af2).
Proof.
  intros.
  destruct H.
  destruct H0.
  split; simpl; intros.

  - (* preview'_set' *)
    rewrite option_fold_bis.
    assert (H :
      option_fold
        (fun y : B =>
         option_fold
           (fun c' : C =>
            option_fold (fun b : B => set' af1 s (set' af2 b c')) s
              (preview' af1 s)) s (preview' af2 y)) s 
        (preview' af1 s) =
      option_fold
        (fun y : B =>
         option_fold
           (fun c' : C => set' af1 s (set' af2 y c')) s (preview' af2 y)) s 
        (preview' af1 s)).
    { destruct (preview' af1); auto. }
    rewrite H.
    clear H.
    admit.

  - (* set'_preview' *)
    simpl in *.
    unfold Basics.compose in *.
    rewrite option_fold_bis.
    rewrite <- (option_fold_f _ _ (preview' af1) _).
    rewrite (fun_ext_with (fun _ => set'_preview'0 _ _)).
    destruct (preview' af1 s); simpl; auto.

  - (* set'_set' *)
    rewrite <- (option_fold_f _ _ (preview' af1) _).
    rewrite (fun_ext_with (fun _ => set'_preview'0 _ _)).
    simpl.
    unfold Basics.compose.
    (* XXX: search for a general theorem *)
    assert (H : option_fold
     (fun s0 : B =>
      option_fold (fun _ : B => Some (set' af2 s0 a1)) None (preview' af1 s))
     (preview' af1 s) (preview' af1 s) =
     option_fold (fun s0 : B => Some (set' af2 s0 a1)) (preview' af1 s) (preview' af1 s)).
    { unfold option_fold.
      destruct (preview' af1 s); auto. }
    rewrite H.
    destruct (preview' af1 s); simpl.
    + rewrite set'_set'0.
      now rewrite set'_set'1.
    + auto.

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
