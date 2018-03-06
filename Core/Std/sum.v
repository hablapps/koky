(** Catamorphism for [sum]. Folds a sum type [A + B] into [C]. *)
Definition sum_fold {A B C} (l : A -> C) (r : B -> C) (s : A + B) : C :=
  match s with
  | inl a => l a
  | inr b => r b
  end.
