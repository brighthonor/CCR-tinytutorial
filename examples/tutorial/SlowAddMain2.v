(*** SPC ***)
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

        def main(): int :=
            return 7;
   *)
  
  Definition mainA: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      ;;;
      Ret (Vint 7).

  
  Definition main_spec: fspec :=
    mk_simple (X:=unit)
      (fun _ =>
         (ord_top,
           (fun varg => (⌜varg = ([]: list val)↑⌝)%I),
           (fun vret => (⌜vret = (Vint 7)↑⌝)%I)
      )).
  
  Definition MainSbtbA: list (string * fspecbody) :=
    [("main", mk_specbody main_spec (cfunU mainA))].

  Definition AMainSem: SModSem.t :=
    {|
      SModSem.fnsems := MainSbtbA;
      SModSem.mn := "Main";
      SModSem.initial_mr := ε;
      SModSem.initial_st := tt↑;
    |}.

  Definition AMain: SMod.t :=
    {|
      SMod.get_modsem := fun _ => AMainSem;
      SMod.sk := [("main", Sk.Gfun)];
    |}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Main: Mod.t := (SMod.to_tgt GlobalStb AMain).

End MID.
