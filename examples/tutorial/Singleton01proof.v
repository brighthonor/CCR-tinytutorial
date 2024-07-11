(*** PROOF ***)
Require Import Singleton0 Singleton1 SingletonRA HoareDef SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import STB.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section PRF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG SingletonRA Σ}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Let W: Type := Any.t * Any.t.

  (* Beware that Union(∨) is not '\' + '/', but '\vee'... *)
  Let wf: _ -> W -> Prop :=
        @mk_wf _ unit
          (fun _ _ st_tgt =>
             ((⌜st_tgt = (1: Z)%Z↑⌝ ** OwnM (Ready))
              ∨ (⌜exists m: Z, m <> 1 /\ Any.downcast st_tgt = Some m⌝ ** OwnM (Fired)))%I).
  
  Theorem correct: refines2 [Singleton0.Singleton] [Singleton1.Singleton GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss; cycle 1.
    { exists tt. red. econs; ss. eapply to_semantic.
      iIntros "H". ss. iLeft. iFrame. iPureIntro. ss. }

    (* singleton *)
    econs; ss.
    { init. unfold singletonF, singletonA.
      harg. mDesOr "INV".
      { mDesAll. des; clarify. steps. force_r; ss. steps. hret _; ss.
        iModIntro. iSplit; ss. iRight.
        iCombine "A" "A1" as "A".
        iEval (rewrite ReadyBall) in "A". iFrame.
        iPureIntro. exists (1 - 1)%Z.
        rewrite Any.upcast_downcast. ss. }
      { mDesAll. des; clarify. steps. force_r; ss.
        steps. force_r.
        mAssertPure False; ss.
        iCombine "A" "A1" as "A".
        iOwnWf "A".
        exfalso.
        eapply FiredBall; ss. steps. }
    }
    
    Unshelve. all: ss. all: try exact 0.
  Qed.
  
End PRF.
