Require Import Core.lens.
Require Import Core.Profunctor.
Require Import Core.Std.fun.

Definition pi1 {A B C} : LensP (prod A C) (prod B C) A B :=
  fun _ _ _ _ => first.

Example proj_1 : pi1 Fun _ _ _ (fun n => n + 1) (0, 0) = (1, 0).
Proof. auto. Qed.
