Require Import Program.Basics.
Require Import Profunctor.
Require Import Util.FunExt.

Open Scope program_scope.

Definition Fun (A B : Type) : Type := A -> B.

Instance Profunctor_fun : Profunctor Fun :=
{ dimap A A' B B' f g ab := g ∘ ab ∘ f
}.

Instance ProfunctorDec_fun : ProfunctorDec Fun.
Proof.
  split; auto.
Qed.

Instance Cartesian_fun : Cartesian Fun :=
{ first  A B C f := fun ac => let (a, c) := ac in pair (f a) c
; second  A B C f := fun ca => let (c, a) := ca in pair c (f a)
}.

Instance CartesianDec_fun : CartesianDec Fun.
Proof.
  split; intros; apply functional_extensionality; intros; destruct x.
  - now destruct u.
  - now destruct p.
Qed.
