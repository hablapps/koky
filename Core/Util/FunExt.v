Require Import FunctionalExtensionality.
Require Export FunctionalExtensionality.

Ltac unwrap_layer := apply f_equal; apply functional_extensionality; intros.

Theorem functional_extensionality_with :
  forall {S T} {f g : S -> T},
    (forall s, f s = g s) -> (fun s => f s) = (fun s => g s).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  now rewrite H.
Qed.

Theorem functional_extensionality_with' :
  forall {S T} {f g : S -> T},
    (forall s, g s = f s) -> (fun s => f s) = (fun s => g s).
Proof.
  intros.
  symmetry in H.
  now rewrite (functional_extensionality_with H).
Qed.
