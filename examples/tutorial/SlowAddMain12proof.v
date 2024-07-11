(*** PROOF_MA ***)
Require Import SlowAddMain1 SlowAddMain2 HoareDef SimModSem.
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
Require Import HTactics HTactics2 ProofMode IPM.
Require Import OpenDef.
Require Import STS STB Invariant.

Require Import MapHeader.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section PRF.

  Context `{Σ: GRA.t}.

  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Hypothesis PUREINCL: forall sk, stb_pure_incl (GlobalStbM sk) (GlobalStb sk).
  
  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
        @mk_wf _ unit
          (fun _ st_src st_tgt => (⌜st_src = tt↑ /\ st_tgt = (3: Z)%Z↑⌝)%I).

  Theorem correct: refines2 [SlowAddMain1.Main GlobalStbM] [SlowAddMain2.Main GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss; cycle 1.
    { exists tt. red. econs; ss. eapply to_semantic. iIntros "H". iFrame. iPureIntro; ss. }
    
    (* main *)
    econs; ss.
    init. 
    rename mp_tgt into mpr_tgt.
    assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
              mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
    { inv WF. esplits; et. } des; clarify.
    harg. fold wf. ss. mDesAll. des; clarify.
    mAssert (True)%I with "". { ss. }
    harg_tgt. { iModIntro. iFrame. iSplit; ss. iAssumption. }
    unfold mainM, mainA, ccallU.
    steps. hAPC _; et. { iIntros "A". iSplit; et. iAssumption. }
    steps.
    hret _; et.
    { iModIntro. iDestruct "FR" as "[% _]".
      iPureIntro. split; ss. }
    { iDestruct "Q" as "[% _]". subst.
      iPureIntro. rr. esplits; et. }

    Unshelve. all: ss. all: try exact 0.
  Qed.
  
End PRF.
