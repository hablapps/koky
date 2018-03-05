Require Import Monad.
Require Import Std.option.
Require Import Util.FunExt.

(** Option transformer, [option] surrounded by an effect [m] *)
Record optionT m `{Monad m} A := mkOptionT
{ runOptionT : m (option A) }.
Arguments mkOptionT [m _ _ _ A].
Arguments runOptionT [m _ _ _ A].

Instance Functor_optionT {m} `{Monad m} : Functor (optionT m) :=
{ fmap _ _ f otx := mkOptionT (fmap (fmap f) (runOptionT otx)) }.

Instance FunctorDec_optionT {m} `{Monad m} : FunctorDec (optionT m).
Proof.
  destruct H0.
  split; simpl; unfold Basics.compose in *; intros.

  - destruct fa.
    apply f_equal.
    unfold id.
    rewrite (fun_ext_with (fun _ => option_fold_id _ _)).
    auto.

  - apply f_equal.
    simpl.
    rewrite (functor_comp _ _ _ _ _ _).
    apply fmap_eq.
    apply functional_extensionality.
    intros.
    now destruct x.
Qed.

Instance Monad_optionT {m} `{Monad m} : Monad (optionT m) :=
{ ret _ x := mkOptionT (ret (Some x))
; bind _ _ otx f := mkOptionT (
    runOptionT otx >>= 
    option_fold (fun x => runOptionT (f x)) (ret None))
}.

Instance MonadDec_optionT {m} `{MonadDec m} : MonadDec (optionT m).
Proof.
  destruct H2.
  split; simpl; intros.

  - (* left_id *)
    rewrite left_id.
    simpl.
    now destruct (f a).
  
  - (* right_id *)
    destruct ma.
    apply f_equal.
    simpl.
    rewrite (fun_ext_with (fun _ => option_fold_f _ _ ret _)).
    rewrite (fun_ext_with_nested ret (fun _ : option A => option_fold_id _ _)).
    auto.

  - (* assoc *)
    apply f_equal.
    unfold option_fold.
    rewrite assoc.
    apply f_equal.
    apply functional_extensionality.
    intros.
    destruct x.
      + unwrap_layer.
        auto.
      + now rewrite left_id.

  - (* fmap rel *)
    apply f_equal.
    unfold Basics.compose in *.
    rewrite (fun_ext_with (fun _ => option_fold_f _ _ ret _)).
    auto.
Qed.
