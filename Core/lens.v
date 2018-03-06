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

(** Very well behaved lens: lens and laws packed together. *)
Record vwbLens S A := mkVwbLens
{ ln : lens S A
; lnDec : lensDec ln
}.
Arguments mkVwbLens [S A].
Arguments ln [S A].
Arguments lnDec [S A].

Instance Category_vwbLens : Category vwbLens :=
{ identity _ := mkVwbLens (mkPLens id (fun _ => id)) _
; compose _ _ _ vwbLn1 vwbLn2 := mkVwbLens (mkPLens 
    (view (ln vwbLn2) ∘ view (ln vwbLn1))
    (fun s => update (ln vwbLn1) s ∘ update (ln vwbLn2) (view (ln vwbLn1) s))) _
}.
Proof.
  split; simpl; intros; auto.
  destruct vwbLn1; destruct lnDec0.
  destruct vwbLn2; destruct lnDec0.
  unfold Basics.compose.
  split; simpl; intros.

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

Instance CategoryDec_vwbLens : CategoryDec vwbLens.
Proof.
  split; intros.

  - (* left_id *)
    admit.

  - (* right_id *)
    admit.

  - (* assoc *)
    admit.

Admitted.

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
