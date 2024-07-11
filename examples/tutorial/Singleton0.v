(*** IMP ***)

Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.

Set Implicit Arguments.

Section IMP.

  Context `{Σ: GRA.t}.
  
  (*
    *** Exmaple in pseudo-code style ***

        int a = 1;
        def singleton(): int :=
            assume(a == 1); // if a <> 1 then the target goes UB
            a = a - 1;
            return 1;
   *)

  Definition singletonF {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E val :=
    fun args =>
      _ <- (pargs [] args)?;;
      a <- trigger PGet;; `a: Z <- a↓?;;
      assume(a = 1%Z);;;
      _ <- trigger (PPut (a - 1: Z)%Z↑);;
      Ret (Vint 1).

  Definition SingletonSem (sk: Sk.t): ModSem.t := {|
    ModSem.fnsems := [("singleton", cfunU singletonF)];
    ModSem.mn := "Singleton";
    ModSem.initial_st := (1: Z)%Z↑;
  |}
  .

  Definition Singleton: Mod.t := {|
    Mod.get_modsem := SingletonSem;
    Mod.sk := [("singleton", Sk.Gfun)];
  |}
  .
  
End IMP.
