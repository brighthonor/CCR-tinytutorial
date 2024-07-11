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
    *** Exmaple in pseudo-code style ***

        def plus(n: int): int :=
            return n + 1;

        def minus(n: int): int :=
            return n - 1;

        def add(n: int, m: int): int :=
            if (m =? 0)
            then return n;
            else return add(plus(n), minus(m));
   *)

  Definition plusF {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E val :=
    fun args =>
      n <- (pargs [Tint] args)?;;
            Ret (Vint (n + 1)).

  Definition minusF {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E val :=
    fun args =>
      n <- (pargs [Tint] args)?;;
            Ret (Vint (n - 1)).
  

  Definition addF {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E val :=
    fun args =>
      '(n, m) <- (pargs [Tint; Tint] args)?;;
      if (m <=? 0)%Z
      then Ret (Vint n)
      else `r1: val <- ccallU "plus" [Vint n];;
           `r2: val <- ccallU "minus" [Vint m];;
           `rr: val <- ccallU "add" [r1; r2];;
           Ret rr.
  
  Definition AddSem (sk: Sk.t): ModSem.t := {|
    ModSem.fnsems := [("plus", cfunU plusF); ("minus", cfunU minusF); ("add", cfunU addF)];
    ModSem.mn := "Add";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Add: Mod.t := {|
    Mod.get_modsem := AddSem;
    Mod.sk := [("plus", Sk.Gfun); ("minus", Sk.Gfun); ("add", Sk.Gfun)];
  |}
  .
  
End IMP.
