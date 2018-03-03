Require Import FunctionalExtensionality.
Require Export FunctionalExtensionality.

Theorem functional_extensionality_with :
  forall {S T} {f g : S -> T},
    (forall s, f s = g s) -> (fun s => f s) = (fun s => g s).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  now rewrite H.
Qed.
