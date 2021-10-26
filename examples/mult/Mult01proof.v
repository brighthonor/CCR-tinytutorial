Require Import HoareDef MultHeader Mult0 Mult1 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import STB ProofMode.
Require Import HTactics.

Set Implicit Arguments.

Local Open Scope nat_scope.


(* Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 '------------------------------------------------------------------' src2 tgt2" *)
(*   := *)
(*     (gpaco8 (_sim_itree wf _) _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) ((Any.pair tgt0 _), tgt2)) *)
(*       (at level 60, *)
(*        format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' "). *)

Section AUX.
  Context `{Σ: GRA.t}.

  Lemma wf_extends
        (x0 x1: Σ)
        (WF: URA.wf x0)
        (EXT: URA.extends x1 x0)
    :
      <<WF: URA.wf x1>>
  .
  Proof. r in EXT. des; clarify. eapply URA.wf_mon; et. Qed.
End AUX.



Section MODE.

  Context `{Σ: GRA.t}.

  Variant mk_wf (A: Type)
          (R: A -> Any.t -> Any.t -> iProp)
    : A -> Any.t * Any.t -> Prop :=
  | mk_wf_intro
      a
      mr_src mr_tgt mp_src mp_tgt
      (RSRC: URA.wf mr_src -> (R a mp_src mp_tgt ** Own mr_tgt) mr_src)
    :
      mk_wf R a ((Any.pair mp_src mr_src↑), (Any.pair mp_tgt mr_tgt↑))
  .

  Local Transparent HoareFun HoareFunArg HoareFunRet HoareCall.

  (* Lemma own_rewrite *)
  (*       r (P: iProp) *)
  (*       (HOLDS: P r) *)
  (*   : *)
  (*     bi_entails (Own r) P *)
  (* . *)
  (* Proof. *)
  (*   uipropall.  i. et. *)
  (* Qed. *)

  (* Lemma harg_clo *)
  (*       A Rn Invsn Invtn *)
  (*       mn r rg *)
  (*       X (P: option mname -> X -> Any.t -> Any.t -> ord -> Σ -> Prop) varg *)
  (*       mpr_src mp_tgt mr_tgt f_tgt k_src *)
  (*       a (le: A -> A -> Prop) *)
  (*       (R: A -> Any.t -> Any.t -> iProp) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)
  (*       (WF: mk_wf R a (mpr_src, (Any.pair mp_tgt mr_tgt↑))) *)
  (*       o_src0 o_src1 o_tgt0 o_tgt1 *)
  (*       (FUEL: o_tgt0 = Ord_S_n o_tgt1 7) *)
  (*       (ARG: *)
  (*          forall x varg_src ord_cur *)
  (*                 ctx (mr_src: Σ) mp_src *)
  (*                 (ACC: current_iPropL ctx [(Rn, P mn x varg_src varg ord_cur); *)
  (*                                          (Invsn, R a mp_src mp_tgt); *)
  (*                                          (Invtn, Own mr_tgt)]), *)
  (*            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a *)
  (*                   (Any.pair mp_src mr_src↑, k_src (ctx, ((mn, x), varg_src, ord_cur))) *)
  (*                   ((Any.pair mp_tgt mr_tgt↑), f_tgt)) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr o_src0 o_tgt0 a *)
  (*            (mpr_src, (HoareFunArg P (mn, varg) >>= k_src)) *)
  (*            ((Any.pair mp_tgt mr_tgt↑), f_tgt) *)
  (* . *)
  (* Proof. *)
  (*   inv WF. *)
  (*   unfold HoareFunArg, mput, mget, assume, guarantee. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intro x. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intro varg_src. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intros (rarg_src, ctx). *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intro VALID. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intro ord_cur. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). i. *)
  (*   eapply Any.pair_inj in H2. des; clarify. eapply Any.upcast_inj in H0. des; clarify. *)
  (*   ired_both. eapply ARG; et. *)
  (*   red. econs. *)
  (*   { instantiate (1:=rarg_src ⋅ mr_src). r_wf VALID. } *)
  (*   { ss. red. rr. *)
  (*     autorewrite with iprop; ss. esplits; et. *)
  (*     assert(T: URA.wf mr_src). *)
  (*     { eapply URA.wf_mon. instantiate (1:=(ctx ⋅ rarg_src)). r_wf VALID. } *)
  (*     spc RSRC. *)
  (*     clear - RSRC T VALID. *)
  (*     uipropall. des. clarify. esplits; et. *)
  (*     { rewrite URA.unit_id; ss. } *)
  (*     { r. uipropall. } *)
  (*   } *)
  (*   Unshelve. all: try exact 0. *)
  (* Qed. *)

  Definition OwnInvT := Own.

  Lemma harg_clo
        A Rn Invsn Invtn
        mn r rg
        X (P: option mname -> X -> Any.t -> Any.t -> ord -> Σ -> Prop) varg
        mp_src mp_tgt (mr_src mr_tgt: Σ) f_tgt k_src
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R a ((Any.pair mp_src mr_src↑), (Any.pair mp_tgt mr_tgt↑)))
        o_src0 o_src1 o_tgt0 o_tgt1
        (FUEL: o_tgt0 = Ord_S_n o_tgt1 7)
        (ARG:
           forall x varg_src ord_cur ctx
                  (ACC: current_iPropL ctx [(Rn, P mn x varg_src varg ord_cur);
                                           (Invsn, R a mp_src mp_tgt);
                                           (Invtn, OwnInvT mr_tgt)]),
             gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a
                    (Any.pair mp_src mr_src↑, k_src (ctx, ((mn, x), varg_src, ord_cur)))
                    (Any.pair mp_tgt mr_tgt↑, f_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr o_src0 o_tgt0 a
             ((Any.pair mp_src mr_src↑), (HoareFunArg P (mn, varg) >>= k_src))
             ((Any.pair mp_tgt mr_tgt↑), f_tgt)
  .
  Proof.
    inv WF.
    unfold HoareFunArg, mput, mget, assume, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step2). intro x.
    repeat (ired_both; gstep; econs; eauto with ord_step2). intro varg_src.
    repeat (ired_both; gstep; econs; eauto with ord_step2). intros (rarg_src, ctx).
    repeat (ired_both; gstep; econs; eauto with ord_step2).
    repeat (ired_both; gstep; econs; eauto with ord_step2). intro VALID.
    repeat (ired_both; gstep; econs; eauto with ord_step2). intro ord_cur.
    repeat (ired_both; gstep; econs; eauto with ord_step2). i.
    eapply Any.pair_inj in H2. des; clarify. eapply Any.upcast_inj in H0. des; clarify.
    eapply Any.pair_inj in H1. des; clarify. eapply Any.upcast_inj in H0. des; clarify.
    ired_both. eapply ARG; et.
    red. econs.
    { instantiate (1:=rarg_src ⋅ mr_src). r_wf VALID. }
    { ss. red. rr.
      autorewrite with iprop; ss. esplits; et.
      assert(T: URA.wf mr_src).
      { eapply URA.wf_mon. instantiate (1:=(ctx ⋅ rarg_src)). r_wf VALID. }
      spc RSRC.
      clear - RSRC T VALID. unfold OwnInvT.
      uipropall. des. clarify. esplits; et.
      { rewrite URA.unit_id; ss. }
      { r. uipropall. }
    }
    Unshelve. all: try exact 0.
  Qed.

  Lemma current_iPropL_pop
        ctx hd tl
        (P: current_iPropL ctx (hd :: tl))
    :
      exists hdr, <<TL: current_iPropL (ctx ⋅ hdr) tl>> ∧ <<HD: hd.2 hdr>>
  .
  Proof.
    rr in P. inv P. destruct hd. ss. unfold from_iPropL in IPROP. fold from_iPropL in IPROP.
    rr in IPROP. rewrite Seal.sealing_eq in *. des. subst. esplits; et.
    rr. econs; et. rewrite URA.add_assoc. rewrite URA.add_comm. rewrite URA.add_assoc. ss.
  Qed.

  Lemma current_iPropL_push
        ctx hdr
        (hd : string * iProp) tl
        (TL: current_iPropL (ctx ⋅ hdr) tl)
        (HD: hd.2 hdr)
    :
        <<P: current_iPropL ctx (hd :: tl)>>
  .
  Proof.
    unfold current_iPropL in *. destruct hd; ss. unfold from_iPropL; fold from_iPropL.
    inv TL.
    econs; et.
    { instantiate (1:=r ⋅ hdr). erewrite f_equal; et. rewrite <- ! URA.add_assoc. f_equal.
      rewrite URA.add_comm. ss. }
    uipropall. esplits; try eassumption. rewrite URA.add_comm. refl.
  Qed.

  Lemma current_iPropL_nil
        ctx
    :
      current_iPropL ctx [] <-> URA.wf ctx
  .
  Proof.
    split; i.
    - rr in H. inv H. rewrite URA.add_comm in GWF. eapply URA.wf_mon; et.
    - rr. unfold from_iPropL. econs; et. { rewrite URA.unit_idl; ss. } r; uipropall.
  Qed.

  Definition Exactly (r0: Σ): iProp' :=
    Seal.sealing
      "iProp"
      (fun r1 => r0 = r1).

  Hint Unfold Exactly: iprop.

  Lemma Exactly_spec
        r0 r1
    :
      Exactly r0 r1 <-> r0 = r1
  .
  Proof. unfold Exactly. uipropall. Qed.

  Lemma harg_clo_tgt
        A Xn Xtra Rn Invtn mp_tgt mr_tgt
        mn r rg
        X (P: option mname -> X -> Any.t -> Any.t -> ord -> Σ -> Prop) varg
        mpr_src f_src k_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R a (mpr_src, Any.pair mp_tgt mr_tgt↑))
        o_src0 o_src1 o_tgt0 o_tgt1
        (FUEL: o_src0 = Ord_S_n o_src1 7)
        ctx x varg_tgt ord_cur
        (ACC: current_iPropL ctx [(Rn, P mn x varg_tgt varg ord_cur); (Invtn, OwnInvT mr_tgt); (Xn, Xtra)])
        (ARG: forall
            rx
            (ACC: current_iPropL ctx [(Rn, P mn x varg_tgt varg ord_cur);
                                     (Invtn, OwnInvT mr_tgt);
                                     (Xn, (Xtra ∧ Exactly rx)%I)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a
                   (mpr_src, f_src)
                   (Any.pair mp_tgt mr_tgt↑, k_tgt (ctx ⋅ rx, ((mn, x), varg_tgt, ord_cur))))
        (* (ARG: *)
        (*    exists x varg_tgt ord_cur *)
        (*           ctx (mr_src: Σ) mp_src mr_tgt mp_tgt *)
        (*           (ACC: current_iPropL ctx [(Rn, P mn x varg_tgt varg ord_cur); *)
        (*                                    (Invsn, R a mp_src mp_tgt); *)
        (*                                    (Invtn, Own mr_tgt)]) *)
        (*    , *)
        (*      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a *)
        (*             (Any.pair mp_tgt mr_tgt↑, f_src) *)
        (*             (Any.pair mp_src mr_src↑, k_tgt (ctx, ((mn, x), varg_tgt, ord_cur)))) *)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr o_src0 o_tgt0 a
             (mpr_src, f_src)
             (Any.pair mp_tgt mr_tgt↑, (HoareFunArg P (mn, varg) >>= k_tgt))
  .
  Proof.
    inv WF.
    unfold HoareFunArg, mput, mget, assume, guarantee. des.
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists x.
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists varg_tgt.
    eapply current_iPropL_pop in ACC. des.
    eapply current_iPropL_pop in TL. des.
    eapply current_iPropL_pop in TL0. des. ss. clear_fast.
    eapply current_iPropL_nil in TL. rename hdr into rarg_src. rename hdr0 into rinv. rename hdr1 into rx.
    apply Any.pair_inj in H2. des; clarify. apply Any.upcast_inj in H0. des; clarify.
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists (rarg_src, (ctx ⋅ rx)).
    repeat (ired_both; gstep; econs; eauto with ord_step2). esplits.
    { clear - TL HD0. rr in HD0. uipropall. rr in HD0. des; clarify.
      eapply wf_extends; et. exists ctx0. r_solve. }
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists ord_cur.
    repeat (ired_both; gstep; econs; eauto with ord_step2). eexists; et.
    ired_both. eapply ARG.
    eapply current_iPropL_push; et.
    eapply current_iPropL_push; et.
    eapply current_iPropL_push; et.
    2: { instantiate (1:=rx). cbn. uipropall. }
    eapply current_iPropL_nil; et.
  Unshelve. all: try exact 0.
  Qed.

  Lemma hret_clo_both
        A (a: shelve__ A)
        mn r rg n m mp_src mp_tgt (mr_src mr_tgt: Σ) a0
        Xs (Qs: option mname -> Xs -> Any.t -> Any.t -> Σ -> Prop)
        Xt (Qt: option mname -> Xt -> Any.t -> Any.t -> Σ -> Prop)
        xs xt vret_src vret_tgt
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (R: A -> Any.t -> Any.t -> iProp) n' m'
        (FUEL: n = Ord_S_n n' 14)
        (FUEL2: m = Ord_S_n m' 14)

        ctx rx
        Invtn Xn Xtra
        (ACC: current_iPropL ctx [(Invtn, OwnInvT mr_tgt); (Xn, (Xtra ∧ Exactly rx)%I)])

        (WLE: le a0 a)

        (UPDATABLE: forall vret_tgt_tgt,
           bi_entails ((Qt mn xt vret_tgt vret_tgt_tgt: iProp) ** Xtra)
                      (bupd (R a mp_src mp_tgt ** (Qs mn xs vret_src vret_tgt: iProp))))

        (EQ: forall (mr_src1 mr_tgt1: Σ) (WLE: le a0 a) vret_tgt_tgt
                    (QT: exists rq, Qt mn xt vret_tgt vret_tgt_tgt rq)
                    (WF: mk_wf R a (Any.pair mp_src mr_src1↑, Any.pair mp_tgt mr_tgt1↑)),
            eqr (Any.pair mp_src mr_src1↑) (Any.pair mp_tgt mr_tgt1↑) vret_tgt vret_tgt_tgt)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a0
             (Any.pair mp_src mr_src↑, (HoareFunRet Qs mn xs (ctx, vret_src)))
             (Any.pair mp_tgt mr_tgt↑, (HoareFunRet Qt mn xt (ctx ⋅ rx, vret_tgt)))
  .
  Proof.
    subst. unfold HoareFunRet, mput, mget, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists vret_tgt.
    steps.
    repeat (ired_both; gstep; econs; eauto with ord_step2).
    rename c0 into mr_tgt1.
    assert (exists mr_src1 rret_src,
               (<<UPDATABLE: URA.wf (ctx ⋅ (mr_tgt1 ⋅ mr_src1 ⋅ rret_src))>>) /\
               (<<RSRC: R a mp_src mp_tgt mr_src1>>) /\
               (<<PRE: Qs mn xs vret_src vret_tgt rret_src>>)).
    { clear - ACC UPDATABLE x0 x1. red in ACC. inv ACC.
      rename x into vret_tgt_tgt. rename c into rt.
      specialize (UPDATABLE vret_tgt_tgt).
      unfold from_iPropL in IPROP.
      uipropall. des. clarify. rename a1 into rx.
      hexploit (UPDATABLE (rt ⋅ rx)); et.
      { eapply wf_extends; try apply x0. r. exists (ctx ⋅ mr_tgt1). r_solve. }
      { instantiate (1:=ctx ⋅ mr_tgt1). r_wf x0. }
      i; des. clarify. esplits; et.
      r_wf H.
    }
    des. exists (rret_src, mr_src1 ⋅ mr_tgt1).
    steps.
    repeat (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits.
    { r_wf UPDATABLE0. }
    repeat (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step2).
    eapply EQ; et. econs; et.
    { ii. uipropall. esplits; et. refl. }
    Unshelve. all: ss.
  Qed.

  Definition HoareCallArg
             (mn: mname)
             (tbr: bool)
             (ord_cur: ord)
             (fsp: fspec):
    gname -> Any.t -> Σ -> (itree Es) _ :=
    fun fn varg_src ctx =>
      '(rarg, fr, mr) <- trigger (Choose (Σ * Σ * Σ));;
      _ <- mput mr;;
      _ <- guarantee(URA.wf (rarg ⋅ fr ⋅ ctx ⋅ mr));;

      x <- trigger (Choose fsp.(meta));; varg_tgt <- trigger (Choose Any.t);;
      ord_next <- trigger (Choose _);;
      _ <- guarantee(fsp.(precond) (Some mn) x varg_src varg_tgt  ord_next rarg);;

      _ <- guarantee(ord_lt ord_next ord_cur /\ (tbr = true -> is_pure ord_next) /\ (tbr = false -> ord_next = ord_top));;
      Ret (x, fr, varg_tgt)
  .

  Definition HoareCallRet
             X
             (mn: mname)
             (tbr: bool)
             (ord_cur: ord)
             (Q: option string → X → Any.t → Any.t → Σ → Prop)
             (vret_tgt: Any.t)
             (x: X)
             (fr: Σ):
    itree Es (Σ * Any.t) :=
      '(rret, ctx) <- trigger (Take (Σ * Σ));;
      mr <- mget;;
      _ <- assume(URA.wf (rret ⋅ fr ⋅ ctx ⋅ mr));;

      vret_src <- trigger (Take Any.t);;
      _ <- assume(Q (Some mn) x vret_src vret_tgt rret);;

      Ret (ctx, vret_src) (*** return to body ***)
  .

  Lemma HoareCall_parse
        (mn: mname)
        (tbr: bool)
        (ord_cur: ord)
        (fsp: fspec)
        (fn: gname)
        (varg_src: Any.t)
        (ctx: Σ):
      HoareCall mn tbr ord_cur fsp fn varg_src ctx =
      '(x, fr, varg_tgt) <- HoareCallArg mn tbr ord_cur fsp fn varg_src ctx;;
      vret_tgt <- trigger (Call fn varg_tgt);;
      HoareCallRet mn tbr ord_cur fsp.(postcond) vret_tgt x fr
  .
  Proof.
    unfold HoareCall, HoareCallArg, HoareCallRet. grind.
  Qed.

  (* Lemma hcall_clo_both *)
  (*       A (a: shelve__ A) *)
  (*       mn r rg n m mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ) a0 *)
  (*       Xs (Qs: option mname -> Xs -> Any.t -> Any.t -> Σ -> Prop) *)
  (*       Xt (Qt: option mname -> Xt -> Any.t -> Any.t -> Σ -> Prop) *)
  (*       xs xt vret_src vret_tgt *)
  (*       (le: A -> A -> Prop) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)
  (*       (R: A -> Any.t -> Any.t -> iProp) n' m' *)
  (*       (FUEL: n = Ord_S_n n' 14) *)
  (*       (FUEL2: m = Ord_S_n m' 14) *)

  (*       ctx0 rx *)
  (*       Invtn Xn Xtra *)
  (*       (ACC: current_iPropL ctx0 [(Invtn, OwnInvT mr_tgt0); (Xn, (Xtra ∧ Exactly rx)%I)]) *)

  (*       (WLE: le a0 a) *)
  (*       tbr ord_cur_src ord_cur_tgt fsp_src fsp_tgt fn varg_src varg_tgt k_src k_tgt *)

  (*       (UPDATABLE: forall vret_tgt_tgt, *)
  (*          bi_entails ((Qt (Some mn) xt vret_tgt vret_tgt_tgt: iProp) ** Xtra) *)
  (*                     (bupd (R a mp_src0 mp_tgt0 ** (Qs (Some mn) xs vret_src vret_tgt: iProp)))) *)

  (*       (EQ: forall (mr_src1 mr_tgt1: Σ) (WLE: le a0 a) vret_tgt_tgt *)
  (*                   (QT: exists rq, Qt (Some mn) xt vret_tgt vret_tgt_tgt rq) *)
  (*                   (WF: mk_wf R a (Any.pair mp_src0 mr_src1↑, Any.pair mp_tgt0 mr_tgt1↑)), *)
  (*           eqr (Any.pair mp_src0 mr_src1↑) (Any.pair mp_tgt0 mr_tgt1↑) vret_tgt vret_tgt_tgt) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a *)
  (*            (Any.pair mp_src0 mr_src0↑, (HoareCall mn tbr ord_cur_src fsp_src fn varg_src) ctx0 >>= k_src) *)
  (*            (Any.pair mp_tgt0 mr_tgt0↑, (HoareCall mn tbr ord_cur_tgt fsp_tgt fn varg_tgt) (ctx0 ⋅ rx) >>= k_tgt) *)
  (* . *)
  (* Proof. *)
  (*   subst. unfold HoareFunRet, mput, mget, guarantee. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). exists vret_tgt. *)
  (*   steps. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). *)
  (*   rename c0 into mr_tgt1. *)
  (*   assert (exists mr_src1 rret_src, *)
  (*              (<<UPDATABLE: URA.wf (ctx ⋅ (mr_tgt1 ⋅ mr_src1 ⋅ rret_src))>>) /\ *)
  (*              (<<RSRC: R a mp_src mp_tgt mr_src1>>) /\ *)
  (*              (<<PRE: Qs mn xs vret_src vret_tgt rret_src>>)). *)
  (*   { clear - ACC UPDATABLE x0 x1. red in ACC. inv ACC. *)
  (*     rename x into vret_tgt_tgt. rename c into rt. *)
  (*     specialize (UPDATABLE vret_tgt_tgt). *)
  (*     unfold from_iPropL in IPROP. *)
  (*     uipropall. des. clarify. rename a1 into rx. *)
  (*     hexploit (UPDATABLE (rt ⋅ rx)); et. *)
  (*     { eapply wf_extends; try apply x0. r. exists (ctx ⋅ mr_tgt1). r_solve. } *)
  (*     { instantiate (1:=ctx ⋅ mr_tgt1). r_wf x0. } *)
  (*     i; des. clarify. esplits; et. *)
  (*     r_wf H. *)
  (*   } *)
  (*   des. exists (rret_src, mr_src1 ⋅ mr_tgt1). *)
  (*   steps. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits. *)
  (*   { r_wf UPDATABLE0. } *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits; eauto. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). *)
  (*   eapply EQ; et. econs; et. *)
  (*   { ii. uipropall. esplits; et. refl. } *)
  (*   Unshelve. all: ss. *)
  (* Qed. *)

  Lemma hcall_clo_ord_weaken' (o_new_src: Ord.t)
        (fsp_src: fspec)
        (o_src: ord) (x_src: shelve__ fsp_src.(meta))
        fsp_tgt 

        A (a0: shelve__ A) FR

        (le: A -> A -> Prop) mn r rg _a n m n' m' mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ)
        k_tgt k_src
        fn tbr ord_cur_src ord_cur_tgt varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (o_new_tgt: Ord.t)


        ctx0 rx
        Invtn Xn Xtra
        (ACC: current_iPropL ctx0 [(Invtn, OwnInvT mr_tgt0); (Xn, (Xtra ∧ Exactly rx)%I)])

        (UPDATABLE: forall x_tgt o_tgt varg_tgt_tgt,
           bi_entails (Xtra ** (fsp_tgt.(precond) (Some mn) x_tgt varg_tgt varg_tgt_tgt o_tgt: iProp))
                      (bupd (FR ** R a0 mp_src0 mp_tgt0 ** (fsp_src.(precond) (Some mn) x_src varg_src varg_tgt o_src: iProp))))

        (FUEL0: n = Ord_S_n n' 10)
        (FUEL1: m = Ord_S_n m' 10)
        (PURE: ord_lt o_src ord_cur_src /\
               (tbr = true -> is_pure o_src) /\ (tbr = false -> o_src = ord_top))
        (SIMPLE: forall x_tgt varg_tgt_tgt o_tgt,
            (bi_entails ((precond fsp_tgt (Some mn) x_tgt varg_tgt varg_tgt_tgt o_tgt): iProp) (⌜varg_tgt = varg_tgt_tgt⌝%I)))

        (POST: forall (vret_tgt : Any.t) (mr_src1 mr_tgt1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1 fr_tgt x_tgt
                      (* (ACC: current_iProp ctx1 (FR ** OwnInvT fr_tgt ** OwnInvT mr_tgt1 *)
                      (*                              ** R a1 mp_src1 mp_tgt1 ** fsp_src.(postcond) (Some mn) x_src vret_src vret_tgt)) *)
                      (ACC: current_iPropL ctx1 [("FR", FR); ("FRT", OwnInvT fr_tgt); ("INV", R a1 mp_src1 mp_tgt1 ** OwnInvT mr_tgt1);
                                                ("POST", fsp_src.(postcond) (Some mn) x_src vret_src vret_tgt)])
          ,
                gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_new_src o_new_tgt _a
                       (Any.pair mp_src1 mr_src1↑, k_src (ctx1, vret_src))
                       (Any.pair mp_tgt1 mr_tgt1↑, HoareCallRet mn tbr ord_cur_tgt fsp_tgt.(postcond) vret_tgt x_tgt fr_tgt >>= k_tgt)
        )
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n _a
             (Any.pair mp_src0 mr_src0↑, (HoareCall mn tbr ord_cur_src fsp_src fn varg_src) ctx0 >>= k_src)
             (Any.pair mp_tgt0 mr_tgt0↑, (HoareCall mn tbr ord_cur_tgt fsp_tgt fn varg_tgt) (ctx0 ⋅ rx) >>= k_tgt)
  .
  Proof.
    subst. rewrite ! HoareCall_parse. unfold HoareCallArg, mput, mget, assume, guarantee.
    steps.
    rename c into mr_tgt1. rename c0 into ro_tgt. rename c1 into fr_tgt.
    assert (exists mr_src1 ro_src fr_src,
               (<<UPDATABLE: URA.wf (ctx0 ⋅ (mr_tgt1 ⋅ mr_src1 ⋅ ro_src ⋅ fr_src ⋅ fr_tgt))>>) /\
               (<<RSRC: R a0 mp_src0 mp_tgt0 mr_src1>>) /\
               (<<FRS: FR fr_src>>) /\
               (<<PRE: fsp_src.(precond) (Some mn) x_src varg_src varg_tgt o_src ro_src>>)).
    { clear - ACC UPDATABLE x x3.
      eapply current_iPropL_pop in ACC; des.
      eapply current_iPropL_pop in TL; des.
      eapply current_iPropL_nil in TL0. ss.
      specialize (UPDATABLE x0 x2 x1).
      rr in HD0. autorewrite with iprop in HD0. des; clarify. r in HD1. autorewrite with iprop in HD1. des; clarify.
      uipropall. exploit UPDATABLE; swap 1 2.
      { esplits; et. }
      { eapply wf_extends; et. r. exists (fr_tgt ⋅ ctx0 ⋅ mr_tgt1). r_solve. }
      { instantiate (1:= fr_tgt ⋅ ctx0 ⋅ mr_tgt1). r_wf x. }
      i; des. clarify.
      esplits; et. r_wf x4.
    }
    des. (ired_both; gstep; econs; eauto with ord_step2).
    exists (ro_src, fr_src ⋅ fr_tgt, mr_src1 ⋅ mr_tgt1).
    steps.
    (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits; eauto.
    { r_wf UPDATABLE0. }
    (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits; eauto.
    (ired_both; gstep; econs; eauto with ord_step2). esplits.
    (ired_both; gstep; econs; eauto with ord_step2). exists o_src.
    (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits; eauto.
    (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits; eauto.
    ired_both.
    assert(x1 = varg_tgt).
    { exploit SIMPLE; et. intros T. uipropall.
      exploit (T ro_tgt); et.
      { eapply wf_extends; try apply x. r. exists (fr_tgt ⋅ ctx0 ⋅ rx ⋅ mr_tgt1). r_solve.  }
      intro U. r in U. uipropall.
    }
    subst.
    steps.
    { econs; et. i. uipropall. esplits; eauto. refl. }
    inv WF.

    unfold HoareCallRet at 1. unfold mget. steps.
    eapply POST; et.
    { eapply current_iPropL_push; et.
      eapply current_iPropL_push; et; cycle 1.
      { cbn. r. uipropall. refl. }
      eapply current_iPropL_push; et; cycle 1.
      { cbn. eapply RSRC0; et. eapply wf_extends; et. exists (c ⋅ fr_src ⋅ fr_tgt ⋅ c0). r_solve. }
      eapply current_iPropL_push; et; cycle 1.
      eapply current_iPropL_nil; et.
      r_wf _ASSUME.
    }
  Unshelve. all: ss.
  Qed.

  (* Lemma hcall_clo_both *)
  (*       Hns Rn Invn *)
  (*       (o: ord) X (x: shelve__ X) *)
  (*       A (a0: shelve__ A) *)

  (*       (P: option mname -> X -> Any.t -> Any.t -> ord -> Σ -> Prop) *)
  (*       (Q: option mname -> X -> Any.t -> Any.t -> Σ -> Prop) *)
  (*       (le: A -> A -> Prop) mn r rg a n m n' mr_src0 mp_src0 *)
  (*       mp_tgt0 k_tgt k_src *)
  (*       fn tbr ord_cur varg_src varg_tgt *)
  (*       (R: A -> Any.t -> Any.t -> iProp) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)

  (*       ctx0 l o_src1 o_tgt1 *)
  (*       (ACC: current_iPropL ctx0 l) *)

  (*       (UPDATABLE: *)
  (*          from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (P (Some mn) x varg_src varg_tgt o: iProp))) *)

  (*       (FUEL: n = Ord_S_n n' 10) *)
  (*       (PURE: ord_lt o ord_cur /\ *)
  (*              (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top)) *)

  (*       (POST: forall (vret_tgt : Any.t) (mr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1 *)
  (*                     (vret_src: Any.t) *)
  (*                     (WLE: le a0 a1) *)
  (*                     ctx1 *)
  (*                     (ACC: current_iPropL ctx1 (@cons (prod string (bi_car iProp)) (Invn, R a1 mp_src1 mp_tgt1) (@cons (prod string (bi_car iProp)) (Rn, Q (Some mn) x vret_src vret_tgt) (snd (alist_pops Hns l))))) *)
  (*         , *)
  (*               gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a *)
  (*                      (Any.pair mp_src1 mr_src1↑, k_src (ctx1, vret_src)) (mp_tgt1, k_tgt vret_tgt)) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a *)
  (*            (Any.pair mp_src0 mr_src0, (HoareCall mn tbr ord_cur (mk_fspec P Q) fn varg_src) ctx0 >>= k_src) *)
  (*            (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt) *)
  (* . *)
  (* Proof. *)
  (*   eapply hcall_clo_weaken; eauto. *)
  (*   { refl. } *)
  (*   { eauto. } *)
  (*   { eauto. } *)
  (* Qed. *)

  Lemma hret_clo_tgt
        A Xn Xtra Rn Frn Invtn mp_tgt mr_tgt
        mn r rg
        X (Q: option mname -> X -> Any.t -> Any.t -> Σ -> Prop)
        mpr_src f_src k_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        o_src0 o_src1 o_tgt0 o_tgt1
        (FUEL: o_src0 = Ord_S_n o_src1 5)
        ctx x vret_tgt vret_src fr_tgt
        (ACC: current_iPropL ctx [(Rn, Q (Some mn) x vret_src vret_tgt); (Frn, OwnInvT fr_tgt); (Invtn, OwnInvT mr_tgt); (Xn, Xtra)])
        (ARG: forall
            rx
            (ACC: current_iPropL ctx [(Rn, Q (Some mn) x vret_src vret_tgt);
                                     (Invtn, OwnInvT mr_tgt);
                                     (Xn, (Xtra ∧ Exactly rx)%I)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a
                   (mpr_src, f_src)
                   (Any.pair mp_tgt mr_tgt↑, k_tgt (ctx ⋅ rx, vret_src)))
        tbr ord_tgt
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr o_src0 o_tgt0 a
             (mpr_src, f_src)
             (Any.pair mp_tgt mr_tgt↑, (HoareCallRet mn tbr ord_tgt Q vret_tgt x fr_tgt >>= k_tgt))
  .
  Proof.
    (* inv WF. *)
    unfold HoareCallRet, mput, mget, assume, guarantee. steps.
    eapply current_iPropL_pop in ACC. des.
    eapply current_iPropL_pop in TL. des.
    eapply current_iPropL_pop in TL0. des.
    eapply current_iPropL_pop in TL. des. ss. clear_fast.
    eapply current_iPropL_nil in TL0. rename hdr into rret. rename hdr1 into rinv. rename hdr0 into rf. rename hdr2 into rx.
    (* apply Any.pair_inj in H2. des; clarify. apply Any.upcast_inj in H0. des; clarify. *)
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists (rret, (ctx ⋅ rx)).
    repeat (ired_both; gstep; econs; eauto with ord_step2). esplits.
    { clear - TL0 HD1 HD0. unfold OwnInvT in *. uipropall. unfold URA.extends in *. des; clarify.
      eapply wf_extends; et. exists (ctx0 ⋅ ctx1). r_solve. }
    steps.
    repeat (ired_both; gstep; econs; eauto with ord_step2). eexists.
    repeat (ired_both; gstep; econs; eauto with ord_step2). eexists; et. steps.
    eapply ARG.
    eapply current_iPropL_push; et.
    eapply current_iPropL_push; et.
    eapply current_iPropL_push; et.
    2: { instantiate (1:=rx). cbn. uipropall. }
    eapply current_iPropL_nil; et.
    { eapply wf_extends; et. exists rf. r_solve. }
  Unshelve. all: try exact 0.
  Qed.

End MODE.

Ltac harg :=
  let PRE := constr:("PRE") in
  let INVS := constr:("INVS") in
  let INVT := constr:("INVT") in
  eapply (@harg_clo _ _ PRE INVS INVT);
  [eassumption
  |refl
  |
  ]; i.



Ltac init :=
  let varg_src := fresh "varg_src" in
  let mn := fresh "mn" in
  let varg := fresh "varg" in
  let EQ := fresh "EQ" in
  let w := fresh "w" in
  let mrp_src := fresh "mrp_src" in
  let mp_tgt := fresh "mp_tgt" in
  let WF := fresh "WF" in
  split; rr; ss; intros varg_src [mn varg] EQ w mrp_src mp_tgt WF;
  (try subst varg_src); eexists _, _; cbn;
  ginit;
  try (unfold fun_to_tgt, cfunN, cfunU; rewrite ! HoareFun_parse); simpl.

Section SIMMODSEM.

  Context `{@GRA.inG fRA Σ}.
  Context `{@GRA.inG gRA Σ}.
  Context `{@GRA.inG hRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ st_tgt => ⌜True⌝%I)
  .

  Theorem correct: refines2 [Mult0.Mult (fun _ => to_stb GlobalStb0)] [Mult1.Mult (fun _ => to_stb GlobalStb1)].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iSplits; ss. }

    econs; [|ss].

    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)



      harg. mDesAll; clarify. steps.
      (*** TODO: use entailment instead ***)
      mAssert (⌜True⌝)%I with "" as "X"; ss.
      mAssert _ with "INVT" as "INVT". { iExact "INVT". }
                                       mAssert (((OwnM fpre ** ⌜ord_top = ord_top⌝) ∧ ⌜varg = varg⌝))%I
                                         with "PRE" as "P".
      { iSplits; ss; et. }
      eapply harg_clo_tgt; et. i.
      clear ACC. mClear "P".

      steps.
      eapply hret_clo_both; et.
      { i. iIntros "H". iDestruct "H" as "[[A _] B]". iModIntro. iFrame. iSplits; et. }
      { i. r. esplits; et. des; clarify. uipropall. des; clarify. rr in QT0. uipropall. }
    }

    econs; [|ss].
    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)



      harg. mDesAll; clarify. steps.
      (*** TODO: use entailment instead ***)
      mAssert (OwnM gpre ** OwnM hpre)%I with "A A1" as "X"; ss.
      { iFrame. }
      mAssert _ with "INVT" as "INVT".
      { iExact "INVT". }
      mAssert (((OwnM fpre ** ⌜ord_top = ord_top⌝) ∧ ⌜varg = varg⌝))%I with "PRE" as "P".
      { iSplits; ss; et. }
      eapply harg_clo_tgt; et. i.
      clear ACC. mClear "P".

      unfold ccallU. steps. stb_tac; clarify. force_l; stb_tac; clarify. steps.
      eapply hcall_clo_ord_weaken'; et.
      { cbn. i. iIntros "H". iModIntro. iDestruct "H" as "[A [[B #C] #D]]".
        iFrame. iSplits; ss; et. iExact "A". }
      { esplits; ss; et. }
      { i. iIntros "H". ss. iDestruct "H" as "[A #B]". eauto. }
      i. ss. clear_fast.
      clear ACC0. mDesAll. clarify. steps. force_l; stb_tac; ss; clarify. steps.

      mAssert (_ ** _) with "FR A" as "X".
      { iSplitL "A"; et. - iExact "A". - iExact "FR". }
      mAssert _ with "A1" as "INVT".
      { iExact "A1". }
      mAssert _ with "FRT" as "FRT".
      { iExact "FRT". }
      mAssert (OwnM gpost ∧ ⌜vret_tgt = vret_tgt⌝)%I with "POST" as "POST"; ss.
      { iSplits; ss; et. }
      eapply hret_clo_tgt; et.
      i. clear ACC. mClear "POST".
      steps. rewrite _UNWRAPU. steps. stb_tac. clarify.



      eapply hcall_clo_ord_weaken'; ss; et.
      { cbn. i. iIntros "[A [% %]]". clarify. iModIntro. iSplitR; iSplits; ss; et.
        { instantiate (1:=True%I). ss. }
        iIntros "[A [#B #C]]". iModIntro. iFrame. iSplits; ss; et. iExact "A". }
      { esplits; ss; et. }
      { i. iIntros "H". ss. iDestruct "H" as "[A #B]". eauto. }
      {


      eapply hret_clo_both; et.
      { i. iIntros "H". iDestruct "H" as "[[A _] B]". iModIntro. iFrame. iSplits; et. }
      { i. r. esplits; et. des; clarify. uipropall. des; clarify. rr in QT0. uipropall. }
    }

  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
