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
Require Import Singleton0 SingletonRA.

Set Implicit Arguments.

Section SPC.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG SingletonRA Σ}.

  (*
   *** Exmaple in pseudo-code style ***

        def singleton(): int :=
            return 1;
   *)
  
  Definition singletonA: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      Ret (Vint 1).

  Definition singleton_spec: fspec :=
    mk_simple (X:=unit)
      (fun _ =>
         (ord_top,
           (fun varg => (⌜varg = ([]: list val)↑⌝ ** (OwnM (Ball)))%I),
           (fun vret => (⌜vret = (Vint 1)↑⌝)%I)
      )).

  Definition SingletonSbtb: list (string * fspecbody) :=
    [("singleton", mk_specbody singleton_spec (cfunU singletonA))].

  Definition SSingletonSem: SModSem.t :=
    {|
      SModSem.fnsems := SingletonSbtb;
      SModSem.mn := "Singleton";
      SModSem.initial_mr := GRA.embed Ready;
      SModSem.initial_st := tt↑;
    |}.

  Definition SSingleton: SMod.t :=
    {|
      SMod.get_modsem := fun _ => SSingletonSem;
      SMod.sk := [("singleton", Sk.Gfun)];
    |}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Singleton: Mod.t := (SMod.to_tgt GlobalStb SSingleton).

End SPC.
