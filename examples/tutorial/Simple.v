Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import SimModSem.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
Require Import HTactics ProofMode.
Require Import OpenDef STB.
Require Import HSim IProofMode.

From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

(*** IMP ***)
Section SIMPLE0.

  Definition simple0_prog {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E val :=
    fun args =>
      _ <- (pargs [] args)?;;
      let r := (Vint 1) in
      r <- (vadd r (Vint 2))?;;
      Ret r.

  Definition Simple0Sem: ModSem.t := {|
    ModSem.fnsems := [("sim", cfunU simple0_prog)]; (* function semantics *)
    ModSem.mn := "Simple"; (* module name *)
    ModSem.initial_st := tt↑; (* initial state *)
  |}.

  Definition Simple0: Mod.t := {|
    Mod.get_modsem := fun _ => Simple0Sem; (* Module Semantics *)
    Mod.sk := [("sim", Sk.Gfun)]; (* same with module semantics *)
  |}.

End SIMPLE0.

(*** SPC ***)
Section SIMPLE1.
  Context `{Σ: GRA.t}.

  Definition simple1_prog {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E val :=
    fun args =>
      _ <- (pargs [] args)?;;
      Ret (Vint 3).

  Definition simple1_prog_spec:    fspec :=
    mk_simple (X:=unit)
              (fun _ => (
                   ord_top,
                   (fun varg =>
                      (⌜varg = ([]: list val)↑⌝)%I
                   ),
                   (fun vret =>
                      (⌜vret = (Vint 3)↑⌝)%I
                   )
              )).

  Definition SimpleSbtb: list (gname * fspecbody) :=
    [("sim", mk_specbody simple1_prog_spec (cfunN simple1_prog))].

  Definition SSimpleSem: SModSem.t := {|
    SModSem.fnsems := SimpleSbtb;
    SModSem.mn := "Simple";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SSimple: SMod.t := {|
    SMod.get_modsem := fun _ => SSimpleSem;
    SMod.sk := [("sim", Sk.Gfun)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Simple: Mod.t := (SMod.to_tgt GlobalStb) SSimple.
  
End SIMPLE1.


(*** PROOF ***)

Section PROOF.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  (* Well-Formed Properties *)
  (* It acts like an invariant. Not needed right now *)
  Let wf: _ -> W -> Prop :=
        mk_wf (fun (_: unit) _ _ => (True: iProp)%I).

  (* Refinement Proof *)
  Theorem correct: refines2 [Simple0] [Simple GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.    
    i. econstructor 1 with (wf:=wf) (le:=top2); et; ss; cycle 1.
    { exists tt. red. econs. eapply to_semantic. iIntros "H". ss. }
    econs; ss.
    (* "sim" Proof Start *)
    init.
    unfold simple0_prog, simple1_prog.
    (* arguments *)
    harg.
    mDesAll. des; clarify.
    (* step - behavior small step *)
    steps.
    (* return value (eapply) *)
    hret _.
    { ss. }
    { iModIntro. iSplit; ss. }
    
    Unshelve. all:ss. all:try exact 0.
  Qed.
  
End PROOF.


(*** HOARE PROOF ***)
Section HOARE.
  Context `{Σ: GRA.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Let W: Type := unit.

  Let le: W -> W -> Prop := top2.

  Let le_PreOrder: @PreOrder unit le.
  Proof. unfold le. econs; eauto. Qed.
  Local Existing Instance le_PreOrder.

  Let wf: W -> Any.t -> Any.t -> iProp :=
        fun _ st_src st_tgt =>
          (⌜st_src = tt↑ /\ st_tgt = tt↑⌝)%I
  .

  Theorem Hcorrect: refines2 [Simple0] [Simple GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss. i. red.
    econstructor 1 with (le:=le) (wf:=mk_wf wf); et; ss; cycle 1.

    { exists tt. econs. eapply to_semantic. iIntros "H". iSplit; ss. }

    econs; ss. econs; ss. red.
    apply isim_fun_to_tgt; auto. i; ss.
    unfold simple0_prog, simple1_prog.
    iIntros "[INV PRE]".
    iDestruct "PRE" as "[% %]". subst.
    iEval (unfold inv_with, wf) in "INV".
    iDestruct "INV" as (w1) "[[% %] %]". des; subst. 
    hred_l. hred_r.
    iApply isim_ret.
    iSplit; ss.
    iPureIntro. exists tt; ss.
  Qed.
  
End HOARE.

(* 2024-05-30 Thr 08:59 *)
