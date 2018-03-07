Require Import Program.Basics.

Open Scope program_scope.

(** Catamorphism for [sum]. Folds a sum type [A + B] into [C]. *)
Definition sum_fold {A B C} (l : A -> C) (r : B -> C) (s : A + B) : C :=
  match s with
  | inl a => l a
  | inr b => r b
  end.

(** A function being applied after fold is the same as composing the very same 
    function with the original constructors and fold with them.  *)
Theorem sum_fold_f :
  forall {A B C D} (l : A -> C) (r : B -> C) (f : C -> D) (apb : A + B),
  @sum_fold A B D (fun a => f (l a)) (fun b => f (r b)) apb = f (sum_fold l r apb).
Proof.
  destruct apb; auto.
Qed.

Theorem sum_fold_fg :
  forall A A1 B B1 C
        (l1 : A -> A1) (l2 : A1 -> C) (r1 : B -> B1) (r2 : B1 -> C) (x : A + B),
    sum_fold l2 r2 (sum_fold (inl ∘ l1) (inr ∘ r1) x) = sum_fold (l2 ∘ l1) (r2 ∘ r1) x.
Proof.
  intros.
  destruct x; auto.
Qed.
