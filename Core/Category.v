(* typeclass and laws *)

(** A class for categories. *)
Class Category (cat : Type -> Type -> Type) :=
{ identity {A} : cat A A 
; compose {A B C} : cat A B -> cat B C -> cat A C
}.
Notation "cab · cbc" := (compose cab cbc) (at level 40, left associativity).

Class CategoryDec (cat : Type -> Type -> Type) `{Category cat} :=
{ left_id : forall A B (cab : cat A B), compose identity cab = cab
; right_id : forall A B (cab : cat A B), compose cab identity = cab
; assoc : forall A B C D (cab : cat A B) (cbc : cat B C) (ccd : cat C D),
            compose cab (compose cbc ccd) = compose (compose cab cbc) ccd 
}.
