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
(* IMP means implementation and it means target program you want to prove by verifying that its behavior is refined with the spec. *)

(* A module is represented as Section in coq. *)
Section SIMPLE0.

  (* Actual Program to prove. Written in Interaction Trees Grammar *)
  Definition simple0_prog {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E val :=
    fun args =>
      _ <- (pargs [] args)?;;
      let r := (Vint 1) in
      r <- (vadd r (Vint 2))?;;
      Ret r.

  (* Implementation Semantics *)
  Definition Simple0Sem: ModSem.t := {|
    ModSem.fnsems := [("sim", cfunU simple0_prog)]; (* function semantics *)
    ModSem.mn := "Simple"; (* module name *)
    ModSem.initial_st := tt↑; (* initial state *)
  |}.

  (* Implementation Module *)
  Definition Simple0: Mod.t := {|
    Mod.get_modsem := fun _ => Simple0Sem; (* Module Semantics *)
    Mod.sk := [("sim", Sk.Gfun)]; (* same with module semantics *)
  |}.

End SIMPLE0.

(*** SPC ***)
(* SPC means the specification program of the implementation. It is usually the most simplified version of the program, however, it can be the middle-stepped version to prove easily in CCR (Composition of the proofs). In spite of its complexity we are going to visit the easiest examples first to enhance the comprehension. *)
Section SIMPLE1.
  Context `{Σ: GRA.t}.

  (* Specification Program *)
  Definition simple1_prog {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E val :=
    fun args =>
      _ <- (pargs [] args)?;;
      Ret (Vint 3).

  (* Precondition & Postcondition *)
  (* For now, the only thing we need to know is the information of in- and output. *)
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

  (* Sbtb (SpecBody TaBle) *)
  Definition SimpleSbtb: list (gname * fspecbody) :=
    [("sim", mk_specbody simple1_prog_spec (cfunN simple1_prog))].

  (* Spec Module Semantics *)
  Definition SSimpleSem: SModSem.t := {|
    SModSem.fnsems := SimpleSbtb;
    SModSem.mn := "Simple";
    SModSem.initial_mr := ε; (* For spec, module resource infos are additionally needed. *)
    SModSem.initial_st := tt↑;
  |}
  .

  (* Spec Module - similiar with the IMP *)
  Definition SSimple: SMod.t := {|
    SMod.get_modsem := fun _ => SSimpleSem;
    SMod.sk := [("sim", Sk.Gfun)];
  |}
  .

  (* Module constructed by the Spec Module *)
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Simple: Mod.t := (SMod.to_tgt GlobalStb) SSimple.
  
End SIMPLE1.


(*** PROOF ***)
(* Let's prove the refinement between IMP and SPC! *)

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
    (* Adequacy : Simulation -> Refinement *)
    (* By applying the adequacy lemma, we could prove the refinement more easily by using the behavior simulation. It enables to use "steps" proving tactic and it makes the proof of the refinement just like Hoare Logic (and Iris). *)
    eapply adequacy_local2. econs; ss.    
    i. econstructor 1 with (wf:=wf) (le:=top2); et; ss; cycle 1.

    (* initial state - it needs to be proved because of the initial state of the resource algebra, in other words, PCM (Partial Commutative Monoid). At now, we don't use any of the RA, therefore "ss" is sufficient. *)
    { exists tt. red. econs. eapply to_semantic. iIntros "H". ss. }

    (* To unshelve one of the function in a program, apply "econs; ss" *)
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
    (* unshelve remained goals and exact values *)
    Unshelve. all:ss. all:try exact 0.
  Qed.
  
End PROOF.


(*** HOARE PROOF ***)
(* Then how about the proof with Iris? Now we prove the same theorem (correct) using Iris tactics (iStartProof, iIntros, etc.). For this, we need to focus on RA, state-relation, and Pre-, Postconditions. *)
Section HOARE.
  Context `{Σ: GRA.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  (* Kripke world *)
  Let W: Type := unit.

  (* world future relation *)
  Let le: W -> W -> Prop := top2.

  Let le_PreOrder: @PreOrder unit le.
  Proof. unfold le. econs; eauto. Qed.
  Local Existing Instance le_PreOrder.

  (* state relation *)
  Let wf: W -> Any.t -> Any.t -> iProp :=
        fun _ st_src st_tgt =>
          (⌜st_src = tt↑ /\ st_tgt = tt↑⌝)%I
  .

  Theorem Hcorrect: refines2 [Simple0] [Simple GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss. i. red.
    econstructor 1 with (le:=le) (wf:=mk_wf wf); et; ss; cycle 1.

    (* initial state - Same with the CCR provig *)
    { exists tt. econs. eapply to_semantic. iIntros "H". iSplit; ss. }

    (* function "sim" *)
    (* To prove with Iris, subtle difference exists in starting proofs *)
    econs; ss. econs; ss. red.
    (* use IPM *)
    apply isim_fun_to_tgt; auto. i; ss.
    (* state relation * precondition |- isim (state relation * postcondition) p_src p_tgt *)
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

(*
  Now we can develop the examples one by one in the following order.

   1) Complex Interaction Trees
      (syscall, recursion, mutual recursion, assume & guarantee)
   2) Preconditon and Postconditon
   3) State Relation
   4) Resource Algebra and Module Resources
   5) Module and Main (function usage)
   6) Composition among the modules
*)

(* 2024-05-30 Thr 08:59 *)
