Require Import Program.Basics.

Open Scope program_scope.

(* typeclass and laws *)

Class Profunctor (p : Type -> Type -> Type) :=
{ dimap {A A' B B'} (f : A' -> A) (g : B -> B') : p A B -> p A' B' 
; lmap {A A' B} (f : A' -> A) : p A B -> p A' B := dimap f id
; rmap {A B B'} (f : B -> B') : p A B -> p A B' := dimap id f
}.

Class ProfunctorDec p `{Profunctor p} :=
{ profunctor_id : forall A B (pab : p A B), dimap id id pab = pab
; profunctor_comp : forall A A' A'' B B' B'' (pab : p A B)
                          (f : A'' -> A') (f' : A' -> A) 
                          (g' : B -> B') (g : B' -> B''),
    dimap (f' ∘ f) (g ∘ g') pab = (dimap f g ∘ dimap f' g') pab
}.

(* cartesian profunctor *)

Class Cartesian p `{ProfunctorDec p} :=
{ first  {A B C} (pab : p A B) : p (prod A C) (prod B C)
; second {A B C} (pab : p A B) : p (prod C A) (prod C B)
}.

(* auxiliar defs to define cartesian laws *)

Definition r1  {A} (a1 : prod A unit) : A := fst a1.
Definition r1' {A} (a: A) : prod A unit := (a, tt).

Definition assoc {A B C} (a_bc : prod A (prod B C)) : prod (prod A B) C :=
  match a_bc with | pair a (pair b c) => pair (pair a b) c end.
Definition assoc' {A B C} (ab_c : prod (prod A B) C) : prod A (prod B C) :=
  match ab_c with | pair (pair a b) c => pair a (pair b c) end.

Class CartesianDec p `{Cartesian p} :=
{ cartesian_unit : forall A B (h : p A B), dimap r1 r1' h = first h
; cartesian_assoc : forall A B C (h : p A A), 
                           dimap assoc assoc' (first (first h)) = @first p _ _ _ A A (prod B C) h
}.
