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
Require Import STB.

Require Import SlowAdd0.

Set Implicit Arguments.

Section SPC.
  Context `{Σ: GRA.t}.

  Definition plus_spec: fspec :=
    mk_simple (X:=nat)
      (fun n => (
               (ord_pure 0),
               (fun varg => (⌜varg = [Vint n]↑⌝)%I),
               (fun vret => (⌜vret = (Vint (n + 1))↑⌝)%I)
      )).

  Definition minus_spec: fspec :=
    mk_simple (X:=nat)
      (fun n => (
               (ord_pure 0),
               (fun varg => (⌜varg = [Vint n]↑⌝)%I),
               (fun vret => (⌜vret = (Vint (n - 1))↑⌝)%I)
      )).

  Definition add_spec: fspec :=
    mk_simple (X:=nat*nat*(Z*Z->Z))
      (fun '(n, m, f_spec) => 
         ((ord_pure (Ord.omega + m)%ord),
           (fun varg =>
              (⌜varg = ([Vint (Z.of_nat n); Vint (Z.of_nat m)]: list val)↑⌝)%I),
           (fun vret => (⌜vret = (Vint (n + m))↑⌝)%I)
      )).
  
  Definition AddSbtb: list (gname * fspecbody) :=
    [("plus", mk_specbody plus_spec (cfunU plusF));
     ("minus", mk_specbody minus_spec (cfunU minusF));
     ("add", mk_specbody add_spec (cfunU addF))].

  Definition SAddSem: SModSem.t :=
    {|
      SModSem.fnsems := AddSbtb;
      SModSem.mn := "Add";
      SModSem.initial_mr := ε;
      SModSem.initial_st := tt↑;
    |}.

  Definition SAdd: SMod.t :=
    {|
      SMod.get_modsem := fun _ => SAddSem;
      SMod.sk := [("plus", Sk.Gfun); ("minus", Sk.Gfun); ("add", Sk.Gfun)];
    |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Add: Mod.t := (SMod.to_tgt GlobalStb) SAdd.

End SPC.
