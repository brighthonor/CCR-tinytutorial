(*** RA ***)
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

Set Implicit Arguments.

(* Same RA with Cannon example *)
Definition SingletonRA: URA.t := Auth.t (Excl.t unit).
Definition Ready: SingletonRA := Auth.black (M:=(Excl.t _)) (Some tt).
Definition Ball: SingletonRA := Auth.white (M:=(Excl.t _)) (Some tt).
Definition Fired: SingletonRA := Auth.excl (M:=(Excl.t _)) (Some tt) (Some tt).

Lemma ReadyBall: Ready ⋅ Ball = Fired.
Proof.
  ur. rewrite URA.unit_idl. ss.
Qed.

Lemma FiredReady: ~ URA.wf (Fired ⋅ Ready).
Proof.
  ur. ss.
Qed.

Lemma FiredBall: ~ URA.wf (Fired ⋅ Ball).
Proof.
  ur. ii. des. ur in H. red in H. des. ur in H. destruct ctx; ss.
Qed.

Lemma BallReady_wf: URA.wf (Ball ⋅ Ready).
Proof.
  ur. split.
  { eexists. rewrite ! URA.unit_id. ss. }
  { ur. ss. }
Qed.
