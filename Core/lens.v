Require Import Program.Basics.
Require Import Std.prod.

Hint Resolve prod_proj.

Open Scope program_scope.

(** Polymorphic lens: views the current part [A] from the whole [S] and updates 
    the part [A] with a new version of it [B], which is reflected in the whole 
    [T]. *)
Record pLens (S T A B : Type) := mkLens
{ view : S -> A
; update : S -> B -> T
}.
Arguments mkLens [S T A B].
Arguments view [S T A B].
Arguments update [S T A B].

(** Monomorphic lens *)
Definition lens S A : Type := pLens S S A A.

Record lensDec {S A} (ln : lens S A) :=
{ view_update : forall s, update ln s (view ln s) = s
; update_view : forall s a, view ln (update ln s a) = a
; update_update : forall s a1 a2, update ln (update ln s a1) a2 = update ln s a2
}.

Definition composeLens {S A B} (ln1 : lens S A) (ln2 : lens A B) : lens S B :=
  mkLens (view ln2 ∘ view ln1)
         (fun s => update ln1 s ∘ update ln2 (view ln1 s)).
Notation "ln1 ▷ ln2" := (composeLens ln1 ln2) (at level 40, left associativity).

(** Provides access to the first component of a product. *)
Definition first {A B} : lens (A * B) A :=
  mkLens fst (fun s a' => (a', snd s)).

Definition firstDec {A B} : lensDec (@first A B).
Proof.
  split; simpl; auto.
Qed.

(** Provides access to the second component of a product. *)
Definition second {A B} : lens (A * B) B :=
  mkLens snd (fun s b' => (fst s, b')).

Definition secondDec {A B} : lensDec (@second A B).
Proof.
  split; simpl; auto.
Qed.
