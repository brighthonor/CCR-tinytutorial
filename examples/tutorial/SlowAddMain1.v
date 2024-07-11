(*** MID ***)
Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.
Require Import ProofMode.

Set Implicit Arguments.

Section MID.

  Context `{Σ: GRA.t}.

  (*
    *** Example in pseudo-code style ***

        int a = 3;
        def main(): int :=
            return a + 4;
   *)
  
  Definition mainM: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      a <- trigger PGet;; `a:Z <- a↓?;;
      ;;;
      Ret (Vint (a + 4)).

  
  Definition main_spec: fspec :=
    mk_simple (X:=unit)
      (fun _ =>
         (ord_top,
           (fun varg => (⌜varg = ([]: list val)↑⌝)%I),
           (fun vret => (⌜vret = (Vint 7)↑⌝)%I)
      )).

  
  Definition MainSbtbM: list (string * fspecbody) :=
    [("main", mk_specbody main_spec (cfunU mainM))].

  Definition SMainSem: SModSem.t :=
    {|
      SModSem.fnsems := MainSbtbM;
      SModSem.mn := "Main";
      SModSem.initial_mr := ε;
      SModSem.initial_st := (3: Z)%Z↑;
    |}.

  Definition SMain: SMod.t :=
    {|
      SMod.get_modsem := fun _ => SMainSem;
      SMod.sk := [("main", Sk.Gfun)];
    |}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Main: Mod.t := (SMod.to_tgt GlobalStb SMain).

End MID.
