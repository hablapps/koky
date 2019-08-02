Require Import Program.Basics.
Require Import Category.
Require Import Std.prod.

Hint Resolve prod_proj.

Open Scope program_scope.

(** Polymorphic lens: views the current part [A] from the whole [S] and updates 
    the part [A] with a new version of it [B], which is reflected in the whole 
    [T]. *)
Record pLens (S T A B : Type) := mkPLens
{ view : S -> A
; update : S -> B -> T
}.
Arguments mkPLens [S T A B].
Arguments view [S T A B].
Arguments update [S T A B].

(** Monomorphic lens *)
Definition lens S A : Type := pLens S S A A.

(** Very well-behaved lens. *)
Record lensDec {S A} (ln : lens S A) := mkLensDec
{ view_update : forall s, update ln s (view ln s) = s
; update_view : forall s a, view ln (update ln s a) = a
; update_update : forall s a1 a2, update ln (update ln s a1) a2 = update ln s a2
}.

Instance Category_lens : Category lens :=
{ identity _ := mkPLens id (fun _ => id) 
; compose _ _ _ ln1 ln2 := mkPLens 
    (view ln2 ∘ view ln1)
    (fun s => update ln1 s ∘ update ln2 (view ln1 s))
}.

Instance CategoryDec_lens : CategoryDec lens.
Proof.
  split; simpl; intros; destruct cab; auto.
Qed.

Lemma lensDec_identity : forall A, lensDec (@identity lens _ A).
Proof. split; auto. Qed.

Lemma lensDec_compose :
  forall {A B C} (ln1 : lens A B) (ln2 : lens B C), 
    lensDec ln1 -> lensDec ln2 -> lensDec (compose ln1 ln2).
Proof.
  intros.
  destruct H.
  destruct H0.
  split; simpl; unfold Basics.compose; intros.

  - (* view_update *)
    rewrite view_update1.
    now rewrite view_update0.

  - (* update_view *)
    rewrite update_view0.
    now rewrite update_view1.

  - (* update_update *)
    rewrite update_update0.
    rewrite update_view0.
    now rewrite update_update1.
Qed.

(** Provides access to the first component of a product. *)
Definition first {A B} : lens (A * B) A :=
  mkPLens fst (fun s a' => (a', snd s)).

Definition firstDec {A B} : lensDec (@first A B).
Proof.
  split; simpl; auto.
Qed.

(** Provides access to the second component of a product. *)
Definition second {A B} : lens (A * B) B :=
  mkPLens snd (fun s b' => (fst s, b')).

Definition secondDec {A B} : lensDec (@second A B).
Proof.
  split; simpl; auto.
Qed.

(** Monadic lens *)

Require Import Monad.

Record mLens (S A : Type) (m : Type -> Type) `{Monad m} := mkMLens
{ mview   : S -> A
; mupdate : S -> A -> m S 
}.

Arguments mkMLens [S A m _ _ _].
Arguments mview [S A m _ _ _].
Arguments mupdate [S A m _ _ _].

(** Well-behaved monadic lens *)

Record mLensLaws {S A m} `{Monad m} (mln : mLens S A m) := mkMLensLaws
{ mview_mupdate : forall s, mupdate mln s (mview mln s) = ret s
; mupdate_mview : forall B (k : S -> A -> m B) s a,
    mupdate mln s a >>= (fun s' => k s' (mview mln s')) =
    mupdate mln s a >>= (fun s' => k s' a)
}.
