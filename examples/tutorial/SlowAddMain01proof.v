(*** PROOF_IM ***)
Require Import SlowAddMain0 SlowAddMain1 SlowAdd1 HoareDef SimModSem.
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

  (* Simple "add" spec for proof *)
  Definition addSpec (x: Z * Z) := match x with (n, m) => (n + m)%Z end.
  
  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
        @mk_wf _ unit
          (fun _ st_src st_tgt => (⌜st_tgt = tt↑ /\ st_src = (3: Z)%Z↑⌝)%I).

  Theorem correct: refines2 [SlowAddMain0.Main] [SlowAddMain1.Main GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss; cycle 1.
    { exists tt. red. econs; ss. eapply to_semantic. iIntros "H". iPureIntro. ss. }
    
    (* main *)
    econs; ss.
    init. harg. mDesAll. des; clarify.
    unfold mainF, mainM, ccallU.
    steps. astart 3. acatch; et.
    hcall (3, 4, addSpec) _ with ""; et.
    { ss. }
    steps. astop. mDesAll. des; clarify. steps.
    hret _; et.

    Unshelve. all: ss. all: try exact 0.
  Qed.
  
End PRF.
