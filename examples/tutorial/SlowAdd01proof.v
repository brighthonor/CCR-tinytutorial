(*** PROOF ***)
Require Import HoareDef OpenDef STB SimModSem.
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

Require Import HTactics ProofMode Invariant.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Require Import SlowAdd0 SlowAdd1.

Set Implicit Arguments.

Section PRF.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ _ => True%I)
  .
  Hypothesis GlobalStb_plus: forall sk,
      GlobalStb sk "plus" = Some plus_spec.
  
  Hypothesis GlobalStb_minus: forall sk,
      GlobalStb sk "minus" = Some minus_spec.

  Hypothesis GlobalStb_add: forall sk,
      GlobalStb sk "add" = Some add_spec.

  Lemma ord_0_lt_omega_Sm: forall n, (0 < Ord.omega + S n)%ord.
  Proof.
    intros.
    apply Ord.lt_trans with Ord.omega.
    apply Ord.omega_upperbound.
    eapply Ord.le_lt_lt.
    { eapply OrdArith.add_base_l. }
    { eapply OrdArith.lt_add_r. rewrite Ord.from_nat_S. eapply Ord.S_lt. }
  Qed.

  Theorem correct: refines2 [SlowAdd0.Add] [SlowAdd1.Add GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2:{ esplits; et. red. econs. eapply to_semantic. et. }
    eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
    hexploit (SKINCL "add"); ss; eauto. intros [blk0 FIND0].
    
    (* plus *)
    econs; ss.
    { unfold plusF. init.
      harg. mDesAll. des; clarify. steps.
      astop. steps. force_l. eexists. steps. hret _; ss. }

    (* minus *)
    econs; ss.
    { unfold minusF. init.
      harg. mDesAll. des; clarify. steps.
      astop. steps. force_l. eexists. steps. hret _; ss. }

    (* add *)
    econs; ss.
    { unfold addF. init.
      harg. destruct x as [[n m] f_spec]. ss. mDesAll. des; clarify. steps.
      des_ifs.
      { astart 0. astop. steps. force_l. eexists. steps. hret _; ss.
        iPureIntro. split; ss. split; ss.
        rewrite Z.leb_le in Heq. assert (m=0) by nia. subst. rewrite Z.add_0_r. ss. }
      destruct m.
      { exfalso. rewrite Z.leb_gt in Heq. lia. }
      unfold ccallU. steps. astart 3. acatch; et.
      hcall _ _ with ""; et.
      { ss. split; ss. apply ord_0_lt_omega_Sm. } steps.
      mDesAll. des; clarify. steps.
      acatch; et.
      hcall (S m) _ with ""; et.
      { ss. split; ss. apply ord_0_lt_omega_Sm. } steps.
      mDesAll. des; clarify. steps.
      acatch; et.
      hcall (_, m, _) _ with ""; et.
      { iPureIntro. repeat split; ss.
        replace (Z.pos (Pos.of_succ_nat m) - 1)%Z with (Z.of_nat m) by nia.
        replace (Vint (n + 1)) with (Vint (n +1)%nat).
        2:{ f_equal. nia. } ss. }
      { ss. split; ss. eauto with ord_step. }
      steps. astop. steps. force_l. mDesAll. des; clarify. eexists. steps.
      hret _; ss.
      iPureIntro. split; ss.
      replace ((n + 1)%nat + m)%Z with (n + Z.pos (Pos.of_succ_nat m))%Z.
      2:{ nia. }
      split; ss.
    }
    
    Unshelve. all: ss. all: try exact 0.
  Qed.
  
End PRF.
