Require Import FunctionalExtensionality.
Require Export FunctionalExtensionality.

(** Useful tactic to deal with with records that contain function fields, such
    as [state]. *)
Ltac unwrap_layer := apply f_equal; apply functional_extensionality; intros.

(** Dives into a function and rewrites the input hypothesis in its body. *)
Theorem fun_ext_with_nested :
  forall {S T U} {f g : S -> T} (h : T -> U),
    (forall s, f s = g s) -> (fun s => h (f s)) = (fun s => h (g s)).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  now rewrite H.
Qed.

(** Same as [fun_ext_with], but reversing the hypothesis. *)
Theorem fun_ext_with_nested' :
  forall {S T U} {f g : S -> T} (h : T -> U),
    (forall s, g s = f s) -> (fun s => h (f s)) = (fun s => h (g s)).
Proof.
  intros.
  symmetry in H.
  now rewrite (fun_ext_with_nested h H).
Qed.

(** Dives into a function and rewrites the whole body with the input 
    hypothesis. *)
Theorem fun_ext_with :
  forall {S T} {f g : S -> T},
    (forall s, f s = g s) -> (fun s => f s) = (fun s => g s).
Proof.
  intros.
  apply (@fun_ext_with_nested S T T f g (fun x => x) H).
Qed.

(** Same as [fun_ext_with], but reversing the hypothesis. *)
Theorem fun_ext_with' :
  forall {S T} {f g : S -> T},
    (forall s, g s = f s) -> (fun s => f s) = (fun s => g s).
Proof.
  intros.
  symmetry in H.
  now rewrite (fun_ext_with H).
Qed.
