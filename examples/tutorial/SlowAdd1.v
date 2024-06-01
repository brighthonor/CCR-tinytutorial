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

  Variable FunStb: Sk.t -> gname -> option fspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Section SKENV.
    Variable sk: Sk.t.

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
                (⌜varg = ([Vint (Z.of_nat n); Vint (Z.of_nat m)]: list val)↑ /\
                  fn_has_spec (FunStb sk) "add"
                    (mk_simple (X:=Z*Z)
                       (fun '(x, y) =>
                          ((ord_pure (Ord.omega)),
                            (fun varg => ⌜varg = ([Vint x; Vint y]: list val)↑⌝),
                            (fun vret => ⌜vret = (Vint (f_spec (x, y)))↑⌝))))⌝)%I),
             (fun vret => (⌜vret = (Vint (n + m))↑⌝)%I)
        )).
    
    Definition AddSbtb: list (gname * kspecbody) :=
      [("plus", ksb_trivial (cfunU plusF));
       ("minus", ksb_trivial (cfunU minusF));
       ("add", mk_kspecbody add_spec (fun _ => triggerUB) (fun _ => triggerNB))].

    Definition KAddSem: KModSem.t :=
      {|
        KModSem.fnsems := AddSbtb;
        KModSem.mn := "Add";
        KModSem.initial_mr := ε;
        KModSem.initial_st := tt↑;
      |}.

  End SKENV.
    
  Definition KAdd: KMod.t := {|
    KMod.get_modsem := KAddSem;
    KMod.sk := [("plus", Sk.Gfun); ("minus", Sk.Gfun); ("add", Sk.Gfun)];
  |}
  .

  Definition Add: Mod.t := (KMod.transl_tgt GlobalStb) KAdd.

End SPC.
