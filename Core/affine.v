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
; preview'_set'a : forall s a,
                     option_fold (fun _ => set' af s a) s (preview' af s) =
                     set' af s a
; set'_preview' : forall s a,
                    preview' af (set' af s a) =
                    fmap (fun _ => a) (preview' af s)
; set'_set' : forall s a1 a2, set' af (set' af s a1) a2 = set' af s a2
}.

(** Affine identity *)
Definition affine'Identity {S} : affine' S S :=
  mkAffine' Some (fun _ => id).

Lemma affine'Dec_identity {S} : affine'Dec (@affine'Identity S).
Proof. split; auto. Qed.

(** Affine composition *)
Definition affine'Compose {A B C}
                          (af1 : affine' A B)
                          (af2 : affine' B C) : affine' A C :=
  mkAffine'
    (fun a => preview' af1 a >>= preview' af2)
    (fun a c' => option_fold
      (fun b => set' af1 a (set' af2 b c')) a (preview' af1 a)).

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Generalizable All Variables.

(* Subrelations to enable [setoid_rewrite] in general settings *)

Instance pointwise_eq_ext {A B : Type} `(sb : subrelation B RB eq)
  : subrelation (pointwise_relation A RB) eq.
Proof.
  intros f g Hfg.
  apply functional_extensionality.
  intro x.
  apply sb, (Hfg x).
Qed.

Instance subrel_eq_respect {A B : Type}
         `(sa : subrelation A RA eq)
         `(sb : subrelation B eq RB) :
   subrelation eq (respectful RA RB).
Proof. intros f g -> a a' Raa'. apply sb. f_equal. apply (sa _ _ Raa'). Qed.

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
    setoid_rewrite <- preview'_set'a1.
    assert (H :
      option_fold
        (fun y : B =>
         option_fold
           (fun c' : C =>
            option_fold
              (fun b : B =>
               set' af1 s
                 (option_fold (fun _ : C => set' af2 b c') b (preview' af2 b))) s
              (preview' af1 s)) s (preview' af2 y)) s (preview' af1 s) =
      option_fold
        (fun y : B =>
         option_fold
           (fun c' : C =>
            option_fold
              (fun b : B =>
               set' af1 s
                 (option_fold (fun c' : C => set' af2 b c') b (preview' af2 b))) s
              (preview' af1 s)) s (preview' af2 y)) s (preview' af1 s)).
    { destruct (preview' af1 s); simpl; auto.
      destruct (preview' af2 b); simpl; auto.
    }
    rewrite H; clear H.
    setoid_rewrite preview'_set'1.
    setoid_rewrite preview'_set'0.
    destruct (preview' af1 s); simpl; auto.
    destruct (preview' af2 b); simpl; auto.

  - (* preview'_set'a *)
    rewrite option_fold_bis.
    assert (H :
      option_fold
        (fun y : B =>
         option_fold
           (fun _ : C =>
            option_fold (fun b : B => set' af1 s (set' af2 b a)) s (preview' af1 s)) s
           (preview' af2 y)) s (preview' af1 s) =
      option_fold
        (fun y : B =>
         option_fold
           (fun _ : C => set' af1 s (set' af2 y a)) s (preview' af2 y))
        s (preview' af1 s)).
    { destruct (preview' af1 s); simpl; auto. }
    rewrite H; clear H.
    setoid_rewrite <- preview'_set'a1 at 2.
    setoid_rewrite <- (option_fold_f _ _ (set' af1 s)).
    assert (H :
      option_fold
        (fun s0 : B => option_fold
          (fun _ : C => set' af1 s (set' af2 s0 a))
          (set' af1 s s0)
          (preview' af2 s0))
        s (preview' af1 s) =
      option_fold
        (fun s0 : B =>
          option_fold
            (fun _ : C => set' af1 s (set' af2 s0 a))
            (option_fold (set' af1 s) s (preview' af1 s))
            (preview' af2 s0))
        s (preview' af1 s)).
    { destruct (preview' af1 s); simpl; auto. }
    rewrite H; clear H.
    now setoid_rewrite preview'_set'0.

  - (* set'_preview' *)
    simpl in *.
    unfold Basics.compose in *.
    rewrite <- (option_fold_f _ _ (preview' af1) _).
    setoid_rewrite set'_preview'0.
    assert (H :
      option_fold (preview' af2) None
        (option_fold
           (fun s0 : B =>
            option_fold
              (fun _ : B =>
               Some (set' af2 s0 a))
              None (preview' af1 s)) (preview' af1 s) (preview' af1 s)) =
      option_fold (preview' af2) None
        (option_fold
           (fun s0 : B => Some (set' af2 s0 a))
           None
          (preview' af1 s))).
    { destruct (preview' af1 s); simpl; auto. }
    rewrite H; clear H.
    rewrite <- (option_fold_f _ _ (option_fold (preview' af2) None) _).
    setoid_rewrite option_fold_bis.
    setoid_rewrite set'_preview'1.
    destruct (preview' af1 s); simpl; auto.

  - (* set'_set' *)
    rewrite <- (option_fold_f _ _ (preview' af1) _).
    rewrite <- (option_fold_f _ _ (option_fold
      (fun b : B =>
       set' af1 (option_fold (fun b0 : B => set' af1 s (set' af2 b0 a1)) s (preview' af1 s))
         (set' af2 b a2))
      (option_fold (fun b : B => set' af1 s (set' af2 b a1)) s (preview' af1 s))) _).
    setoid_rewrite set'_preview'0.
    simpl.
    unfold Basics.compose.
    destruct (preview' af1 s); simpl; auto.
    rewrite set'_set'0.
    now rewrite set'_set'1.
Qed.

(** Left identity *)
Lemma affine'_left_identity :
  forall A B (af : affine' A B),
    affine'Dec af -> affine'Compose affine'Identity af = af.
Proof.
  intros.
  unfold affine'Compose.
  unfold affine'Identity.
  destruct H.
  destruct af.
  apply f_equal.
  extensionality a.
  now extensionality c'.
Qed.

(** Righ identity *)
Lemma affine'_right_identity :
  forall A B (af : affine' A B),
    affine'Dec af -> affine'Compose af affine'Identity = af.
Proof.
  intros.
  unfold affine'Compose.
  unfold affine'Identity.
  destruct H.
  destruct af.
  simpl.
  rewrite (fun_ext_with (fun _ => option_fold_id _ _)).
  apply f_equal.
  extensionality a.
  extensionality c'.
  now rewrite preview'_set'a0.
Qed.

Lemma affine'_associativity :
  forall A B C D (af1 : affine' A B) (af2 : affine' B C) (af3 : affine' C D),
    affine'Dec af1 -> affine'Dec af2 -> affine'Dec af3 ->
    affine'Compose (affine'Compose af1 af2) af3 =
    affine'Compose af1 (affine'Compose af2 af3).
Proof.
  unfold affine'Compose.
  simpl.
  intros.
  assert (G :
    (fun a : A =>
      option_fold (preview' af3) None
        (option_fold (preview' af2) None (preview' af1 a))) =
    (fun a : A =>
      option_fold (fun a0 : B => option_fold (preview' af3) None (preview' af2 a0))
        None (preview' af1 a))).
  { extensionality a.
    destruct (preview' af1 a); simpl; auto. }
  rewrite G. clear G.
  apply f_equal.
  extensionality a.
  extensionality c'.
  assert (G :
    option_fold
      (fun b : C =>
       option_fold (fun b0 : B => set' af1 a (set' af2 b0 (set' af3 b c'))) a
         (preview' af1 a)) a (option_fold (preview' af2) None (preview' af1 a)) =
    option_fold
      (fun b => option_fold
                  (fun c => set' af1 a (set' af2 b (set' af3 c c')))
                  a (preview' af2 b))
      a (preview' af1 a)).
  { destruct (preview' af1 a); simpl; auto. }
  rewrite G; clear G.
  destruct H0.
  rewrite (fun_ext_with' (fun _ => option_fold_f _ _ (set' af1 a) _)).
  assert (G :
    option_fold
      (fun s : B =>
       option_fold (fun a0 : C => set' af1 a (set' af2 s (set' af3 a0 c')))
         (set' af1 a s) (preview' af2 s)) a (preview' af1 a) =
    option_fold
      (fun s : B =>
       option_fold (fun a0 : C => set' af1 a (set' af2 s (set' af3 a0 c')))
         (option_fold (set' af1 a) a (preview' af1 a)) (preview' af2 s)) a (preview' af1 a)).
  { destruct (preview' af1 a); simpl; auto. }
  rewrite G; clear G.
  destruct H.
  assert (G :
    (fun s : B =>
       option_fold (fun a0 : C => set' af1 a (set' af2 s (set' af3 a0 c')))
         (option_fold (set' af1 a) a (preview' af1 a)) (preview' af2 s)) =
    (fun s : B =>
       option_fold (fun a0 : C => set' af1 a (set' af2 s (set' af3 a0 c')))
         a (preview' af2 s))).
  { extensionality s.
    now rewrite preview'_set'1. }
  now rewrite G.
Qed.

(** Provides access to the head of a list. *)
Definition head {A} : affine (list A) A :=
  mkPAffine (fun s => option_fold inl (inr nil) (hd_error s)) (fun s a' =>
    match s with
    | _ :: t => a' :: t
    | Nil => Nil
    end).

Definition headDec {A} : affineDec (@head A).
Proof.
  split; intros s; destruct s; auto.
Qed.
