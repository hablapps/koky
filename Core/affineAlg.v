Require Import Std.option.
Require Import optionT.
Require Import naturalTrans.
Require Import MonadState.
Require Import Program.Basics.
Require Import Logic.FunctionalExtensionality.

Open Scope program_scope.


(* generic stuff *)

Definition fork {A B C} (f : A -> B) (g : A -> C) : A -> B * C := fun a => (f a, g a).
Notation "f △ g" := (fork f g) (at level 36, left associativity).

Definition join {A B C} (f : B -> A) (g : C -> A) : B + C -> A :=
  fun bc => match bc with | inl b => f b | inr c => g c end.
Notation "f ▽ g" := (join f g) (at level 36, left associativity).

Definition fprod {A B C D} (f : A -> B) (g : C -> D) : A * C -> B * D :=
  fun ac => (f (fst ac), g (snd ac)).
Notation "f * g" := (fprod f g) (at level 40, left associativity).

Definition fsum {A B C D} (f : A -> B) (g : C -> D) : A + C -> B + D :=
  fun ac => match ac with | inl a => inl (f a) | inr c => inr (g c) end.
Notation "f + g" := (fsum f g) (at level 50, left associativity).

Definition distl {A B C} : A * (B + C) -> A * B + A * C := fun abc => 
  let (a, bc) := abc in match bc with
  | inl b => inl (a, b)
  | inr c => inr (a, c)
  end.

Definition distr {A B C} : (A + B) * C -> A * C + B * C := fun abc => 
  let (ab, c) := abc in match ab with
  | inl a => inl (a, c)
  | inr b => inr (b, c)
  end.

Definition apply {A B} (fa : (A -> B) * A) : B := let (f, a) := fa in f a.


(* generic theories *)

Property prod_after_prod : 
  forall A B C D E F (f : B -> C) (g : E -> F) (h : A -> B) (k : D -> E), 
    (f * g ) ∘ (h * k) = (f ∘ h) * (g ∘ k).
Proof.
  intros.
  apply functional_extensionality; intros.
  now destruct x.
Qed.

Property idxid_is_id : forall A B, id * id = @id (A * B)%type.
Proof.
  intros.
  apply functional_extensionality; intros.
  now destruct x.
Qed.

Property left_id : forall A B (f : A -> B), id ∘ f = f.
Proof. intros; apply functional_extensionality; auto. Qed.

Property right_id : forall A B (f : A -> B), f ∘ id = f.
Proof. intros; apply functional_extensionality; auto. Qed.

Property fun_assoc : 
  forall A B C D (f : A -> B) (g : B -> C) (h : C -> D),
    h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. intros. now apply functional_extensionality. Qed.


(* state monad *)

Definition state S Out := S -> Out * S.

Instance Functor_state S : Functor (state S) :=
{ fmap _ _ f sa := (f * id) ∘ sa }.

Instance FunctorDec_state S : FunctorDec (state S).
Proof.
  constructor; intros; unfold fmap, Functor_state; simpl.
  - now rewrite idxid_is_id, left_id.
  - unfold Basics.compose at 1.
    now rewrite fun_assoc, prod_after_prod.
Qed.

Instance Monad_state S : Monad (state S) :=
{ ret _ x := const x △ id
; bind _ _ sa f := apply ∘ (f * id) ∘ sa
}.

Instance MonadDec_state S : MonadDec (state S).
Proof.
  constructor; intros; simpl; apply functional_extensionality; auto.
  intros.
  unfold Basics.compose.
  now destruct (ma x).
Qed.

Instance MonadState_state S : MonadState S (state S) :=
{ get := id △ id
; put s' := const tt △ const s' 
}.

Instance MonadStateDec_state S : MonadStateDec S (state S).
Proof.
  constructor; intros; now apply functional_extensionality.
Qed.


(* classic affine *)

Record affine S A := mkAffine
{ preview : S -> A + unit
; set : S * A -> S
}.
Arguments mkAffine [S A].
Arguments preview [S A].
Arguments set [S A].

Record affineDec {S A} (af : affine S A) :=
{ preview_set : set af ▽ fst ∘ distl ∘ id △ preview af = id
; preview_set' : set af ▽ fst ∘ distr ∘ ((fst + fst) * id) ∘ (distl * id) ∘ ((id △ preview af) * id) = set af
; set_preview : preview af ∘ set af = (snd + fst) ∘ distr ∘ (preview af * id)
; set_set : set af ∘ (set af * id) = set af ∘ (fst * id)
}.


(* natural affine *)

Definition affine' S A := state A ~> optionT (state S).

Record affine'Dec {S A} (φ : affine' S A) :=
{ law1 : forall X Y (m : state A X) (k : X -> state A Y), 
    runNaturalTrans φ (m >>= (fun x => k x)) = 
    runNaturalTrans φ m >>= (fun x => runNaturalTrans φ (k x))
; law2 : forall X Y (m : state A X) (y : Y), 
    runNaturalTrans φ m >> runNaturalTrans φ (ret y) = 
    runNaturalTrans φ m >> ret y
}.


(* transformation *)

Definition optionToSum (A : Type) (oa : option A) : A + unit :=
  match oa with | Some a => inl a | None => inr tt end.

Definition affine2affine' S A (φ: affine' S A): affine S A :=
{| preview := fun s => optionToSum (evalIndexedStateT (runOptionT (runNaturalTrans φ get)) s)

|}.
