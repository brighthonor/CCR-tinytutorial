(*** IMP ***)
Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.


Set Implicit Arguments.

Section IMP.

  Context `{Σ: GRA.t}.

  (*
    *** Example in pseudo-code style ***

        def main(): int :=
            return slow_add(3, 4);
   *)

  Definition mainF {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E val :=
    fun args =>
      _ <- (pargs [] args)?;;
      `a: val <- ccallU "add" ([Vint 3; Vint 4]);;
      Ret a.

  Definition MainSem: ModSem.t :=
    {|
      ModSem.fnsems := [("main", cfunU mainF)];
      ModSem.mn := "Main";
      ModSem.initial_st := tt↑;
    |}.

  Definition Main: Mod.t :=
    {|
      Mod.get_modsem := fun _ => MainSem;
      Mod.sk := [("main", Sk.Gfun)];
    |}.

End IMP.
