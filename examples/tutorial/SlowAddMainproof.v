(*** PROOF_IM ***)
Require Import SlowAddMain0 SlowAddMain2 SlowAdd1 HoareDef SimModSem.
Require Import SlowAddMain01proof SlowAddMain12proof.
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

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  
  Hypothesis GlobalStb_add: forall sk,
      GlobalStb sk "add" = Some add_spec.
  
  Theorem correct: refines2 [SlowAddMain0.Main] [SlowAddMain2.Main GlobalStb].
  Proof.
    etrans.
    { eapply SlowAddMain01proof.correct. apply GlobalStb_add. }
    { eapply SlowAddMain12proof.correct. i. ss. }
  Qed.

End PRF.
