Require Import Core.lens.
Require Import Core.Std.option.

Class Eq (A : Type) :=
{ eq (a1 a2 : A) : bool
}.

(** Partiality *)

Definition constMLens (A B : Type) (b : B) `{Eq B} : mLens A B option :=
  mkMLens (fun _ => b) (fun a b' => if eq b b' then Some a else None).
