Require Import List.
Require Import Arith.Max.
Require Import Arith.Lt.
Require Import Arith.Le.
Require Import Arith.PeanoNat.
Require Import Arith.Plus.

Require Import defns.
Require Import nl_fusion.
Require Import nl_sgn.
Require Import nl_whr.
Require Import nl_eq.
Require Import nl_struct.



(** inversion of algdepth w.r.t whr **)


(** depth auxiliaries **)
(*
Fixpoint depth_K (L:nK) : nat :=
  match L with
  | kindstar_nl_type => 0
  | (kindstar_nl_pi_intro nA nL) => S (depth_K nL)
end.

Lemma cstu_K_depth:
  forall (L L' : nK) (n : nat),
    n = depth_K L -> cstu_nK L L' -> n = depth_K L'.
Proof.
  intros.
  generalize dependent L.
  generalize dependent L'.
  induction n.
  intros.
  destruct L.
  inversion H0.
  auto.
  inversion H.
  (* step *)
  intros.
  destruct L'.
  inversion H0.
  rewrite <- H1 in H.
  inversion H.
  destruct L.
  inversion H.
  cbv.
  f_equal.
  apply IHn with L.
  inversion H.
  reflexivity.
  inversion H0.
  assumption.
Qed.

Fixpoint depth_nTy (A:nTy) : nat :=
  match A with
  | (typestar_nl_tcon tcon) => 0
  | (typestar_nl_pi_intro A B) => S (max (depth_nTy A) (depth_nTy B))
  | (typestar_nl_pi_elim A N) => S (depth_nTy A)
end.

Require Import Arith.Compare_dec.

Lemma cstu_nTy_depth':
  forall (m n : nat), n <= m -> 
  forall (A A' : nTy), 
    n = depth_nTy A -> cstu_nTy A A' -> n = depth_nTy A'.
Proof.
  induction m.
  (* case m = 0 *)
  intros.
  destruct n.
  destruct A.
  inversion H1.
  rewrite H0.
  auto.
  replace (depth_nTy (typestar_nl_pi_intro A1 A2))
    with (S (max (depth_nTy A1) (depth_nTy A2)))
    in H0 by (cbv; auto).
  inversion H0.
  replace (depth_nTy (typestar_nl_pi_elim A nte5))
    with (S (depth_nTy A))
    in H0 by (cbv; auto).
  inversion H0.
  inversion H.
  (* case m = S m' *)
  intros.
  inversion H1.
  rewrite H0.
  rewrite <- H2.
  auto.
  (* pi_intro *)
  replace (depth_nTy (typestar_nl_pi_intro nA' nB'))
    with (S (max (depth_nTy nA') (depth_nTy nB')))
    by (cbv; auto).
  rewrite <- H4 in H0.
  replace (depth_nTy (typestar_nl_pi_intro nA nB))
    with (S (max (depth_nTy nA) (depth_nTy nB)))
    in H0 by (cbv; auto).
  rewrite H0.
  f_equal.
  remember (depth_nTy nA).
  remember (depth_nTy nB).
  assert (n0 = depth_nTy nA').
  apply IHm with nA.
  apply lt_n_Sm_le.
  apply lt_le_trans with n.
  rewrite H0.
  apply le_lt_n_Sm.
  apply le_max_l.
  assumption.
  assumption.
  assumption.
  assert (n1 = depth_nTy nB').
  apply IHm with nB.
  apply lt_n_Sm_le.
  apply lt_le_trans with n.
  rewrite H0.
  auto with arith.
  auto.
  auto.
  auto.
  auto.
  (* elim case *)
  destruct n.  
  rewrite <- H4 in H0.
  replace ( depth_nTy (typestar_nl_pi_elim nA nM))
    with (S (depth_nTy nA)) in H0 by (cbv; auto).
  inversion H0.
  (* step *)
  replace ( depth_nTy (typestar_nl_pi_elim nA' nM'))
    with (S (depth_nTy nA')) by (cbv; auto).
  f_equal.
  rewrite <- H4 in H0.
  replace ( depth_nTy (typestar_nl_pi_elim nA nM))
  with (S (depth_nTy nA)) in H0 by (cbv; auto).
  apply IHm with nA.
  auto with arith.
  auto.
  auto.
Qed.  

Lemma cstu_nTy_depth:
  forall (n : nat) (A A' : nTy),
    n = depth_nTy A -> cstu_nTy A A' -> n = depth_nTy A'.
Proof.
  intros.
  eauto using cstu_nTy_depth'.
Qed.

Fixpoint depth_nte (M :nte) : nat :=
  match M with
  | (termstar_nl_con c) => 0
  | (termstar_nl_ixc ixc) => ixc
  | (termstar_nl_ixt ixt) => ixt
  | (termstar_nl_pi_intro A M) => S (depth_nte M)
  | (termstar_nl_pi_elim M N) => S (max (depth_nte M) (depth_nte N))
  end.

*)
(*
TODO: Accessible relation akin to:

Fixpoint algdepth (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy)
         (H1 : algeq_nl_te sS sG M N tau) : nat :=
  match H1 with
  | algeq_nl_te_whr_l _ _ _ _ _ _ _ algeqM'N => S (| algeqM'N |)
  | algeq_nl_te_whr_r _ _ _ _ _ _ _ algeqMN' => S (| algeqMN' |)
  | algeq_nl_te_streq _ _ _ _ _ streqMN => S (| streqMN |)
  | algeq_nl_te_eta_exp _ _ _ _ _ _ _ _ _ _ algeqM'N' => S (| algeqM'N' |)
  end.
with strdepth ...
  math H2 with
  | streq_nl_te_zero               => 0
  | streq_nl_te_succ               => 0
  | streq_nl_te_con                => 0
  | streq_nl_te_pi_elim            => max (| streqM1N1 |) (| algeq M2N2 |)
  end.
*)


(*
Definition eqdepth (sS : nsgn) (sG : nctx) (M N : nte) (tau : snTy) : nat :=
  match (M, N, tau) with
  | (termstar_nl_con c0, termstar_nl_con c1, tau) => 0
  | (termstar_nl_ixc ixc, term_nl_icx, tau) => ixc
  | (termstar_nl_pi_elim M1 N1, termstar_nl_pi_elim M2 N2, tau) => max (M1 N1 tau) 
  | (_, _, _) => 0
  end.
*)

Fixpoint strdepth_nte (M : nte) : nat :=
  match M with
  | (termstar_nl_con c) => 0
  | (termstar_nl_ixc ixc) => ixc
  | (termstar_nl_ixt ixt) => 0
  | (termstar_nl_pi_intro A M) => 0
  | (termstar_nl_pi_elim M N) => S (strdepth_nte M)
  end.



Fixpoint algdepth_snTy (tau : snTy) : nat :=
  match tau with
  | (stype_nl_tcon a) => 0
  | (stype_nl_pi_intro tau1 tau2) => S (algdepth_snTy tau2)
end.

(* number of whr steps *)
Fixpoint algdepth_nte (M : nte) : nat :=
  match M with
  | (termstar_nl_con c) => 0
  | (termstar_nl_ixc ixc) => 0
  | (termstar_nl_ixt ixt) => 0
  | (termstar_nl_pi_intro A M) => 0
  | (termstar_nl_pi_elim (termstar_nl_pi_intro A M) N) => S (algdepth_nte M + algdepth_nte N)
  | (termstar_nl_pi_elim M N) => S (algdepth_nte M) 
end.

Definition algdepth (M N : nte) (tau1 tau2 : snTy) : nat :=
  (algdepth_nte M) + (algdepth_nte N) +
  (max (algdepth_snTy tau1) (algdepth_snTy tau2)).

Lemma algdepth_whr_l:
  forall (M N : nte) (tau1 tau2 : snTy),
    algdepth M N tau1 tau2 <= 0 -> forall M' , ~whr_nl_te M M'.
Proof.
(*  intros.
  intro.
  unfold algdepth in H.
  inversion H0.
  rewrite <- H2 in H.
  replace ((algdepth_nte (termstar_nl_pi_elim (termstar_nl_pi_intro nA nM) nN)))
  with (S (algdepth_nte nM + algdepth_nte nN))  in H by (cbv; auto).
  assert (S (algdepth_nte nM + algdepth_nte nN) <= 0).
  eauto with arith.
  inversion H4.
  (* whr head case *)
  rewrite <- H2 in H.
  replace ((algdepth_nte (termstar_nl_pi_elim nM nN)))
  with (S (algdepth_nte nM)).
  admit.
  destruct nM; cbv; auto.
  
    in H by (destruct nM; cbv; auto).
  assert (Nat.max (S (algdepth_nte nM)) (algdepth_nte N)
          <= (Nat.max (S (algdepth_nte nM)) (algdepth_nte N)
              + Nat.max (algdepth_snTy tau1) (algdepth_snTy tau2) )).
  auto with arith.
  assert (Nat.max (S (algdepth_nte nM)) (algdepth_nte N) <= 0).
  eauto with arith.
  assert ((S (algdepth_nte nM)) <= max (S (algdepth_nte nM)) (algdepth_nte N)).
  auto with arith.
  assert (S (algdepth_nte nM) <= 0).
  eauto with arith.
  inversion H7.
Qed.   
 *)
Admitted.

Lemma algdepth_whr_r:
  forall (M N : nte) (tau1 tau2  : snTy),
    algdepth M N tau1 tau2 <= 0 -> forall N' , ~whr_nl_te N N'.
Proof.
(*  intros.
  intro.
  unfold algdepth in H.
  inversion H0.
  rewrite <- H2 in H.
  replace ((algdepth_nte (termstar_nl_pi_elim (termstar_nl_pi_intro nA nM) nN)))
          with 1 in H by (cbv; auto).
  assert (Nat.max (algdepth_nte M) 1
          <= (Nat.max (algdepth_nte M) 1
              +  Nat.max (algdepth_snTy tau1) (algdepth_snTy tau2)
             ))
    by (auto with arith).
  assert (Nat.max (algdepth_nte M) 1 <= 0) by (eauto using le_trans).
  assert (1 <= max (algdepth_nte M) 1) by (auto with arith).
  assert (1 <= 0) by (eauto with arith).
  inversion H7.
  (* whr head case *)
  rewrite <- H2 in H.
  replace ((algdepth_nte (termstar_nl_pi_elim nM nN)))
  with (S (algdepth_nte nM)) in H by (destruct nM; cbv; auto).
  assert (Nat.max (algdepth_nte M) (S (algdepth_nte nM))
          <= (Nat.max (algdepth_nte M) (S (algdepth_nte nM))
              + Nat.max (algdepth_snTy tau1) (algdepth_snTy tau2)
             )).
  auto with arith.
  assert (Nat.max (algdepth_nte M) (S (algdepth_nte nM)) <= 0).
  eauto with arith.
  assert ((S (algdepth_nte nM)) <= max (algdepth_nte M) (S (algdepth_nte nM))).
  auto with arith.
  assert (S (algdepth_nte nM) <= 0) by (eauto with arith).
  inversion H7.
Qed.   
 *)
(*
Admitted.

Lemma algdepth_pi_intro_l:
  forall (M N : nte) (tau0 tau1 tau2 : snTy),
    ~ (algdepth M N (stype_nl_pi_intro tau0 tau1) tau2 <= 0).
Proof.
  intros.
  unfold algdepth.
  replace ((algdepth_snTy (stype_nl_pi_intro tau0 tau1)))
          with (S (algdepth_snTy tau1)) by (cbv; auto).
  intro.
  assert (S (algdepth_snTy tau1) <= 0).
  eauto with arith.
  inversion H0.
Qed.

Lemma algdepth_pi_intro_r:
  forall (M N : nte) (tau0 tau1 tau2 : snTy),
    ~ (algdepth M N tau0 (stype_nl_pi_intro tau1 tau2) <= 0).
Proof.
  intros.
  unfold algdepth.
  replace ((algdepth_snTy (stype_nl_pi_intro tau1 tau2)))
          with (S (algdepth_snTy tau2)) by (cbv; auto).
  intro.
  assert (S (algdepth_snTy tau2) <= 0).
  eauto with arith.
  inversion H0.
Qed.


Lemma algdepth_whr:
  forall (M M' : nte),   
    whr_nl_te M M' ->
    algdepth_nte M' < algdepth_nte M.
Proof.
Admitted.
*)
  
  
Lemma algeq_nl_te_streq:
  forall (n : nat) (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    (algdepth_snTy tau = n) ->
    ( algeq_nl_te sS sG M N tau ) ->
    ( streq_nl_te sS sG M N tau ).
Proof.
  intro.
  induction n.
  intros.
  admit.

  intros.
  destruct tau.
  inversion H.
  inversion H0.

  inversion H.
  assert (streq_nl_te sS (tau1 :: sG)
         (termstar_nl_pi_elim nM' (termstar_nl_ixc 0))
         (termstar_nl_pi_elim nN' (termstar_nl_ixc 0)) tau2
         ).
  eapply IHn.
  exact H11.
  exact H9.
  inversion H10.


  
Lemma algeq_nl_te_streq_determinacy':
  forall (n m : nat) (sS : snsgn) (sG : snctx) (M N : nte) (tau tau' : snTy),
    (algdepth_snTy tau = n ) ->
    (algdepth_snTy tau' = m ) ->
    ( algeq_nl_te sS sG M N tau ) ->
    ( algeq_nl_te sS sG M N tau' ) ->
    tau = tau'.
Proof.
  induction n, m.
  admit.
  (* step *)
  admit.
  admit.
  
  intros.
  destruct tau.
  inversion H.
  inversion H.
  destruct tau'.
  inversion H0.
  inversion H0.
  f_equal.

(*
Lemma algeq_nl_te_tag:
  forall (d : mstralgeq ) (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    ( algeqB_nl_te sS sG d M N tau) ->
    ( algeq_nl_te sS sG M N tau)
with streq_nl_te_tag:
  forall (d : mstralgeq ) (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    ( streqB_nl_te sS sG d M N tau) ->
    ( streq_nl_te sS sG M N tau).
Proof.
  (* lemma 1 *)
  intros.
  induction H.
  eapply algeq_nl_te_whr_l; eauto.
  eapply algeq_nl_te_whr_r; eauto.
  eapply algeq_nl_te_streq.
  eapply streq_nl_te_tag; eauto.
  eapply algeq_nl_te_eta_exp; eauto.
  (* lemma 2 *)
  intros.
  induction H.
  constructor; auto.
  constructor; auto.
  constructor; auto.
  eapply streq_nl_te_pi_elim.
  eauto.
  eapply algeq_nl_te_tag.
  eauto.
Qed.
*)

  (*
Lemma algeq_nl_te_determinacy_tau_tcon:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (a a' : tcon) (tau : snTy),
    ( algeq_nl_te sS sG M N (stype_nl_pi_intro tau (stype_nl_tcon a))) ->
    ( streq_nl_te sS sG M N (stype_nl_tcon a')) ->
    False.
Proof.
  intros.
  inversion H.
  destruct M.
  inversion H3.
  destruct N.
  inversion H8.
  rewrite <- H10 in H9.
  rewrite <- H12 in H9.
  inversion H9.
  inversion H15; inversion H24.
  inversion H15; inversion H24.
  inversion H19.
  inversion H27.
  inversion H0.
  assert (stype_nl_pi_intro tau3 (stype_nl_tcon a) = stype_nl_tcon a')
         by (eapply boundsnCon_determinacy; eauto).
  inversion H43.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  (* M ~ ixc *)
  destruct N.
  inversion H0.
  inversion H3.
  inversion H8.
  rewrite <- H10 in H9.
  rewrite <- H12 in H9.
  inversion H9.
  inversion H15; inversion H24.
  inversion H15; inversion H24.
  inversion H19; inversion H27.
  inversion H27; rewrite H41 in H0.
  assert (stype_nl_pi_intro tau3 (stype_nl_tcon a) = stype_nl_tcon a')
         by (eapply streq_nl_te_strong_determinacy; eauto).
  inversion H45.
  inversion H0.
  inversion H0.
  inversion H0.
  (* ixt *)
  inversion H0.
  inversion H0.
  (* pi_elim *)
  inversion H3.
  rewrite <- H13 in H9.
  inversion H9.
  inversion H16.
  assert ({M3 | cs_nte M3 nM'2}) by (admit).
  destruct H26.
  apply whr_nl_te_cs_inversion with (M := termstar_nl_pi_elim M1 M2) (M' := x) in H25.
  apply streq_nl_te_determinacy_l in H0.
  destruct H0.
  exists x.
  assumption.
  constructor; auto.
  auto.
  inversion H0.
  rewrite <- H27 in H8; inversion H8.
  rewrite <- H33 in H16; inversion H16.
  assert ({M3 | cs_nte M3 nM'2}) by (admit).
  destruct H39.
  apply whr_nl_te_cs_inversion with (M := termstar_nl_pi_elim nN2 nN3) (M' := x) in H38.
  apply streq_nl_te_determinacy_r in H0.
  destruct H0.  
  exists x.
  rewrite <- H27; auto.
  constructor; auto.
  auto.
  (* pi elim *)
  inversion H20.

Lemma algeq_nl_te_determinacy_tau_tcon:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (a : tcon) (tau : snTy),
    ( algeq_nl_te sS sG M N tau) ->
    ( algeq_nl_te sS sG M N (stype_nl_tcon a)) ->
    tau = (stype_nl_tcon a).
Proof.
  intros.
  generalize dependent a.
  induction H.
  intros.
  admit.
  intros.
  admit.
  admit.

Lemma algeq_nl_te_determinacy_tau_tcon:
  forall (sS : snsgn) (sG : snctx) (M N M' N' : nte) (a : tcon) (tau1 tau2 : snTy),  
  cs_nte M M' ->
  cs_nte N N' ->
  algeq_nl_te sS (tau1 :: sG)
         (termstar_nl_pi_elim M' (termstar_nl_ixc 0))
         (termstar_nl_pi_elim N' (termstar_nl_ixc 0)) tau2 ->
  algeq_nl_te sS sG M N (stype_nl_pi_intro tau1 tau2). 
Proof.
  intros.
  generalize dependent N.
  generalize dependent M.
  generalize dependent tau1.
  generalize dependent sG.
  induction tau2.
  intros.
  admit.
  intros.
  eapply algeq_nl_te_eta_exp.
  exact H.
  exact H0.
  eapply IHtau2_2.
  inversion H1.
*)
 


(*

Lemma streq_nl_te_algeq:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau tau' : snTy),
    (streq_nl_te sS sG M N tau') ->
    (algeq_nl_te sS sG M N tau) ->
    (tau = tau').
Proof. 
  intros.
  generalize dependent H.
  generalize dependent tau'.
  induction H0.
  intros.
  apply streq_nl_te_determinacy_l in H1.
  destruct H1.
  eexists; eauto.
  intros.
  apply streq_nl_te_determinacy_r in H1.
  destruct H1.
  eexists; eauto.
  intros.
  eapply streq_nl_te_strong_determinacy; eauto.
  intros.
  destruct tau'.
  apply algeq_nl_te_streq in H2.
  
  

  
Lemma algeq_nl_te_simpl:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    algeq_nl_te sS sG M N tau ->
    (exists M' N', whr_nl_te M M' /\ whr_nl_te N N' /\ streq_nl_te sS sG M' N' tau) \/
    (exists M', whr_nl_te M M' /\ streq_nl_te sS sG M' N tau) \/
    (exists N', whr_nl_te N N' /\ streq_nl_te sS sG M N' tau) \/
    (streq_nl_te sS sG M N tau).                                                              
Proof.
  intros.
  induction H.
  destruct IHalgeq_nl_te.
  destruct H1.
  destruct H1.
  destruct H1.
  admit.
  destruct H1.
  destruct H1.
  destruct H1.
  admit.
  destruct H1.
  destruct H1.
  destruct H1.
  left.
  exists nM'.
  exists x.
  split.
  auto.
  split; auto.
  right.
  left.
  exists nM'.
  split; auto.
  destruct IHalgeq_nl_te.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  admit.
  destruct H1.
  destruct H1.
  destruct H1.
  left.
  exists x.
  exists nN'.
  split.
  auto.
  split; auto.
  destruct H1.
  destruct H1.
  destruct H1.
  admit.
  right.
  right.
  left.
  exists nN'.
  split; auto.
  right; right; right.
  auto.
  destruct IHalgeq_nl_te.
  destruct H2.
  destruct H2.
  
  
  exists x0.
  assumption.
  
    
  
  admit.
  admit.
  assumption.
  inversion IHalgeq_nl_te.
  inversion H10.
  inversion H11.
  inversion H11.
  inversion H11.


  STOP

*)
  

(*
Lemma algdepth_pi_elim:
  forall (M M' N N' : nte) (tau1 tau2 : snTy),
    cs_nte M M' -> cs_nte N N' ->
    algdepth (termstar_nl_pi_elim M' (termstar_nl_ixc 0))
    (termstar_nl_pi_elim N' (termstar_nl_ixc 0)) tau2
    < algdepth M N (stype_nl_pi_intro tau1 tau2).
Proof.
Admitted.



Lemma algdepth_pi_intro:
  forall (M N : nte) (tau1 tau2 : snTy),
    ~ (0 = algdepth M N (stype_nl_pi_intro tau1 tau2)).
Proof.
  intros.
  intro.
  destruct M.
  destruct N.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  destruct N.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  destruct N.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  destruct N.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  destruct N.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
Qed.   

Lemma algdepth_whr_l:
  forall (M N M' : nte) (tau : snTy),
    whr_nl_te M M' ->
    ~ (0 = algdepth M N tau).
Proof.
  intros.
  intro.
  inversion H.
  rewrite <- H2 in H0.
  destruct N.
  destruct tau.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  rewrite <- H2 in H0.
  destruct N.
  destruct tau.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.  
Qed.

Lemma algdepth_whr_r:
  forall (M N N' : nte) (tau : snTy),
    whr_nl_te N N' ->
    ~ (0 = algdepth M N tau).
Proof.
  intros.
  intro.
  inversion H.
  rewrite <- H2 in H0.
  destruct M.
  destruct tau.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  rewrite <- H2 in H0.
  destruct M.
  destruct tau.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.
  inversion H0.  
Qed.

Require Import Arith.Plus.


Lemma algdepth_nte_pos:
  forall (M : nte),
    0 < algdepth_nte M.
Proof.
  intros.
  destruct M.  
  auto.
  auto.
  auto.
  auto.
  replace (algdepth_nte (termstar_nl_pi_elim M1 M2))
  with (S (algdepth_nte M1)) by (cbv; auto).
  auto with arith.
Qed.

Lemma algdepth_tuts:
  forall (M N M' : nte),
    tuts_nte M N M' ->
    algdepth_nte M' < algdepth_nte M + algdepth_nte N.
Proof.
  induction M.
  intros; inversion H.
  assert (0 < algdepth_nte N) by (auto using algdepth_nte_pos).
  auto with arith.
  intros; inversion H.
  assert (0 < algdepth_nte N) by (auto using algdepth_nte_pos).
  auto with arith.
  intros; inversion H.
  assert (0 < algdepth_nte N) by (auto using algdepth_nte_pos).
  auto with arith.
  assert (0 < algdepth_nte N) by (auto using algdepth_nte_pos).
  auto with arith.  
  intros; inversion H.
  assert (0 < algdepth_nte N) by (auto using algdepth_nte_pos).
  auto with arith.
  intros; inversion H.
  assert (0 < algdepth_nte N) by (auto using algdepth_nte_pos).
  replace (algdepth_nte (termstar_nl_pi_elim nM' nN'))
          with (S (algdepth_nte nM')) by (cbv; auto).
  replace (algdepth_nte (termstar_nl_pi_elim M1 M2) + algdepth_nte N)
  with (S (algdepth_nte M1 + algdepth_nte N)) by (cbv; auto).
  apply lt_n_S.
  apply IHM1.
  assumption.
Qed.  
  
Lemma algdepth_cs:
  forall (M M' : nte),
    cs_nte M M' -> (algdepth_nte M') <= S (algdepth_nte M).
Proof.
  induction M.
  intros.
  inversion H.
  auto.
  intros; inversion H.
  auto.
  intros.
  inversion H.
  auto.
  intros.
  inversion H.
  auto.
  intros.
  inversion H.
  cbv.
  apply le_n_S.
  apply IHM1.
  assumption.
Qed.
  
Lemma algdepth_cs_strong:
  forall (M M' N N' : nte) (tau1 tau2 : snTy),
    cs_nte M M' ->
    cs_nte N N' ->
    algdepth (termstar_nl_pi_elim M' (termstar_nl_ixc 0))
    (termstar_nl_pi_elim N'  (termstar_nl_ixc 0)) tau2 < algdepth M N (stype_nl_pi_intro tau1 tau2).
Proof.
  unfold algdepth.
  intros.
  replace (algdepth_snTy (stype_nl_pi_intro tau1 tau2))
      with ((algdepth_snTy tau2)) by (cbv; auto).
  apply plus_lt_compat_r.
  apply plus_le_lt_compat.
  apply le_S_n.
  apply le_trans with (algdepth_nte N').
  admit.
  admit.
  admit.
Admitted.

Lemma algdepth_le_whr_l:
  forall (M N M' : nte) (a : tcon),
    whr_nl_te M M' ->
    algdepth M' N (stype_nl_tcon a) < algdepth M N (stype_nl_tcon a).
Proof.
  intros.
  apply plus_lt_compat_r.
  apply plus_lt_compat_r.
  apply algdepth_whr.
  assumption.
Qed.

Lemma algdepth_le_whr_r:
  forall (M N N' : nte) (a : tcon),
    whr_nl_te N N' ->
    algdepth M N' (stype_nl_tcon a) < algdepth M N (stype_nl_tcon a).
Proof.
  intros.
  apply plus_lt_compat_r.
  apply plus_lt_compat_l.
  auto using algdepth_whr.
Qed.

Lemma phony:
  forall (n : nat) (M N : nte) (tau : snTy),
    algdepth M N tau <= n.
Admitted.

*)

(*
Lemma streq_nl_te_dec:
  forall (m n : nat) (sS : snsgn) (sG : snctx) (M N : nte),
    n <= m -> n = depth_nte M -> wfssig_nl sS -> 
    { tau | streq_nl_te sS sG M N tau } + { forall tau , ~ streq_nl_te sS sG M N tau}.
Proof.  
  intro.
  induction m.
  (* depth 0 *)
  intros.
  destruct M.
  destruct N.
  assert ({tau | boundsnCon con5 tau sS} +
          {forall tau , ~boundsnCon con5 tau sS}) by (apply boundsnCon_dec).
  assert ({con5 = con0} + {con5 <> con0}) by (apply eq_tcon).
  destruct H2.
  destruct H3.
  left.
  rewrite <- e.
  destruct s.
  exists x.
  apply streq_nl_te_con. 
  assumption.
  assumption.
  right.
  intros.
  intro.
  inversion H2.
  contradiction.
  right.
  intros.
  intro.
  inversion H2.
  apply n0 with tau.
  rewrite H5.
  assumption.
  (* con ~ ixc *)
  right.
  intros; intro.
  inversion H2.
  (* con ~ ixt *)
  right.
  intros; intro.
  inversion H2.
  (* con ~ pi_intro *)
  right.
  intros; intro.
  inversion H2.
  (* con ~ pi_elim *)
  right.
  intros; intro.
  inversion H2.
  (* ixc cases *)
  destruct N.
  right.
  intros; intro.
  inversion H2.
  (* ixc ~ ixc *)
  assert ({ixc = ixc0} + {ixc <> ixc0}) by (apply Nat.eq_dec).
  destruct H2.
  destruct sG.
  (* empty ctx *)
  right.
  intros; intro.
  inversion H2.
  (* nonempty ctx *)
  destruct ixc.
  left.
  rewrite <- e.
  exists s.
  apply streq_nl_te_var_zero.
  assumption.
  replace (depth_nte (termstar_nl_ixc (S ixc))) with (S ixc) in H0 by (cbv; auto).
  rewrite H0 in H.
  apply le_n_0_eq in H.
  inversion H.
  right; intros; intro.
  inversion H2.
  rewrite H3 in H6.
  contradiction.
  rewrite H3 in H4.
  contradiction.
  (* ixc ~ ixt *)
  right.
  intros; intro.
  inversion H2.
  (* ixc ~ pi_intro *)
  right.
  intros; intro.
  inversion H2.
  (* ixc ~ pi_elim *)
  right.
  intros; intro.
  inversion H2.
  (* ixt cases *)
  right.
  intros; intro.
  inversion H2.
  (* pi_intro cases *)
  right.
  intros.
  intro.
  inversion H2.
  (* pi_elim cases *)
  destruct N.
  (* pi_elim ~ con *)
  right.
  intros; intro.
  inversion H2.
  (* pi_elim ~ ixc *)
  right.
  intros; intro.
  inversion H2.
  (* pi_elim ~ ixt *)
  right.
  intros; intro.
  inversion H2.
  (* pi_elim ~ pi_intro *)
  right.
  intros; intro.
  inversion H2.
  (* pi_elim ~ pi_elim *)
  replace (depth_nte (termstar_nl_pi_elim M1 M2)) with (S (max (depth_nte M1) (depth_nte M2)))
   in H0 by (cbv;auto).
  apply le_n_0_eq in H.
  rewrite <- H in H0.
  inversion H0.
  (* step cases *)
  intros.
  destruct M.
  (* con *)
  destruct N.
  assert ({tau | boundsnCon con5 tau sS} +
          {forall tau , ~boundsnCon con5 tau sS}) by (apply boundsnCon_dec).
  assert ({con5 = con0} + {con5 <> con0}) by (apply eq_tcon).
  destruct H2.
  destruct H3.
  left.
  rewrite <- e.
  destruct s.
  exists x.
  apply streq_nl_te_con. 
  assumption.
  assumption.
  right.
  intros.
  intro.
  inversion H2.
  contradiction.
  right.
  intros.
  intro.
  inversion H2.
  apply n0 with tau.
  rewrite H5.
  assumption.
  (* con ~ ixc *)
  right.
  intros; intro.
  inversion H2.
  (* con ~ ixt *)
  right.
  intros; intro.
  inversion H2.
  (* con ~ pi_intro *)
  right.
  intros; intro.
  inversion H2.
  (* con ~ pi_elim *)
  right.
  intros; intro.
  inversion H2.
  (* ixc cases *)
  destruct N.
  right.
  intros; intro.
  inversion H2.
  (* ixc ~ ixc *)
  assert ({ixc = ixc0} + {ixc <> ixc0}) by (apply Nat.eq_dec).
  destruct H2.
  destruct sG.
  (* empty ctx *)
  right.
  intros; intro.
  inversion H2.
  (* nonempty ctx *)
  destruct ixc.
  replace (depth_nte (termstar_nl_ixc 0)) with 0 in H0 by (cbv; auto).
  rewrite <- e.
  left.
  exists s.
  apply streq_nl_te_var_zero.
  assumption.
  rewrite <- e.
  assert ({tau | streq_nl_te sS sG (termstar_nl_ixc ixc) (termstar_nl_ixc ixc) tau} +
        {forall tau , ~ streq_nl_te sS sG (termstar_nl_ixc ixc) (termstar_nl_ixc ixc) tau}).
  apply IHm with ixc.
  replace (depth_nte (termstar_nl_ixc (S ixc))) with (S ixc) in H0 by (cbv; auto).
  rewrite H0 in H.
  auto with arith.
  cbv; auto.
  assumption.
  inversion H2.
  left.
  destruct H3.
  exists x.
  apply streq_nl_te_var_succ.
  assumption.
  assumption. 
  right.
  intros; intro.
  inversion H4.
  apply H3 with tau.
  assumption.
  right; intros; intro.
  inversion H2.
  rewrite H3 in H6.
  contradiction.
  rewrite H3 in H4.
  contradiction.
  (* ixc ~ ixt *)
  right.
  intros; intro.
  inversion H2.
  (* ixc ~ pi_intro *)
  right.
  intros; intro.
  inversion H2.
  (* ixc ~ pi_elim *)
  right.
  intros; intro.
  inversion H2.
  (* ixt cases *)
  right.
  intros; intro.
  inversion H2.
  (* pi_intro cases *)
  right.
  intros; intro.
  inversion H2.
  (* pi_elim cases *) 
  destruct N.
  (* pi_elim ~ con *)
  right.
  intros; intro.
  inversion H2.
  (* pi_elim ~ ixc *)
  right.
  intros; intro.
  inversion H2.
  (* pi_elim ~ ixt *)
  right.
  intros; intro.
  inversion H2.
  (* pi_elim ~ pi_intro *)
  right.
  intros; intro.
  inversion H2.
  (* pi_elim ~ pi_elim *)
  assert ({tau | streq_nl_te sS sG M1 N1 tau} +
          {forall tau , ~ streq_nl_te sS sG M1 N1 tau}).  
  remember (depth_nte M1).
  apply IHm with n0.
  replace (depth_nte (termstar_nl_pi_elim M1 M2)) with (S (max (depth_nte M1) (depth_nte M2))) in H0 by (cbv; auto).
  rewrite <- Heqn0 in H0.
  rewrite H0 in H.
  apply le_S_n in H.
  apply le_trans with (Nat.max n0 (depth_nte M2)).
  apply le_max_l.
  assumption.
  assumption.
  assumption.
  destruct H2.
  destruct s.
  destruct x.
  right.
  intros; intro.
  inversion H2.
  assert ( (stype_nl_tcon tcon5) = (stype_nl_pi_intro tau2 tau)).
  eauto using streq_nl_te_strong_determinacy.
  inversion H12.
  assert ({tau1 | algeq_nl_te sS sG M2 N2 tau1} +
        {forall tau1 , ~ algeq_nl_te sS sG M2 N2 tau1}).
  admit. (* from mutual lemma *)
  destruct H2.
  destruct s0.
  assert ({x = x1} + {x <> x1}) by (decide equality; apply eq_con).
  destruct H2.
  left.
  exists x2.
  apply streq_nl_te_pi_elim with x1.
  assumption.
  rewrite <- e.
  assumption.
  right.
  intros; intro.
  inversion H2.
  assert ( (stype_nl_pi_intro x1 x2) =  (stype_nl_pi_intro tau2 tau)).
  eauto using streq_nl_te_strong_determinacy.
  inversion H12.
  assert (x = tau2) by admit. (*(eauto using algeq_nl_te_strong_determinacy).*)
  apply n0.
  rewrite H13; rewrite H14; auto.
  right.
  intros; intro.
  inversion H2.
  apply n0 with tau2.
  assumption.
  right.
  intros; intro.
  inversion H2.
  apply n0 with (stype_nl_pi_intro tau2 tau).
  assumption.
Admitted.
*)


(* MAIN THEOREM *)
(*
Fixpoint streq_nl_te_dec' (n : nat)
  (sS : snsgn) (sG : snctx) (M N : nte) {struct n}:
    depth_nte M <= n -> wfssig_nl sS -> 
    { tau | streq_nl_te sS sG M N tau } + { forall tau , ~ streq_nl_te sS sG M N tau}
with algeq_nl_te_dec' (n m : nat) 
  (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy) {struct m}:
    m <= n -> algdepth M N tau = m ->
    wfssig_nl sS ->
    { algeq_nl_te sS sG M N tau } + {~ algeq_nl_te sS sG M N tau}.
Proof.
*)

(*
Fixpoint algeq_nl_te_dec'' (n m : nat) 
  (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy) {struct m}:
    m <= n -> algdepth M N tau = m ->
    wfssig_nl sS ->
    { algeq_nl_te sS sG M N tau } + {~ algeq_nl_te sS sG M N tau}.
Admitted.
 *)

(*Fixpoint streq_nl_te_dec' (n : nat) (sS : snsgn) (sG : snctx) (M N : nte)
  (algeq_lemma : forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
       wfssig_nl sS -> {algeq_nl_te sS sG M N tau} + {~ algeq_nl_te sS sG M N tau}) {struct n} :
    depth_nte M <= n -> wfssig_nl sS -> 
    { tau | streq_nl_te sS sG M N tau } + { forall tau , ~ streq_nl_te sS sG M N tau}
.*)
(*
Lemma streq_nl_te_dec':
  forall (sS : snsgn) (sG : snctx) (M N : nte),
    wfssig_nl sS -> 
    { tau | streq_nl_te sS sG M N tau } + { forall tau , ~ streq_nl_te sS sG M N tau}.
  (* Lemma 1 *)
  intros.
  
  generalize dependent N.
  generalize dependent M.
  generalize dependent sG.
  generalize dependent sS.
  induction n.
  
  (* depth 0 *)
  intros.
  destruct M.
  destruct N.
  assert ({tau | boundsnCon con5 tau sS} +
          {forall tau , ~boundsnCon con5 tau sS}) by (apply boundsnCon_dec).
  assert ({con5 = con0} + {con5 <> con0}) by (apply eq_tcon).
  destruct H1.
  destruct H2.
  left.
  rewrite <- e.
  destruct s.
  exists x.
  apply streq_nl_te_con. 
  assumption.
  assumption.
  right.
  intros.
  intro.
  inversion H1.
  contradiction.
  right.
  intros.
  intro.
  inversion H1.
  apply n with tau.
  rewrite H4.
  assumption.
  (* con ~ ixc *)
  right.
  intros; intro.
  inversion H1.
  (* con ~ ixt *)
  right.
  intros; intro.
  inversion H1.
  (* con ~ pi_intro *)
  right.
  intros; intro.
  inversion H1.
  (* con ~ pi_elim *)
  right.
  intros; intro.
  inversion H1.
  (* ixc cases *)
  destruct N.
  right.
  intros; intro.
  inversion H1.
  (* ixc ~ ixc *)
  assert ({ixc = ixc0} + {ixc <> ixc0}) by (apply Nat.eq_dec).
  destruct H1.
  destruct sG.
  (* empty ctx *)
  right.
  intros; intro.
  inversion H1.
  (* nonempty ctx *)
  destruct ixc.
  left.
  rewrite <- e.
  exists s.
  apply streq_nl_te_var_zero.
  assumption.
  replace (depth_nte (termstar_nl_ixc (S ixc))) with (S ixc) in H by (cbv; auto).
  apply le_n_0_eq in H.
  inversion H.
  right; intros; intro.
  inversion H1.
  rewrite H2 in H5.
  contradiction.
  rewrite H2 in H3.
  contradiction.
  (* ixc ~ ixt *)
  right.
  intros; intro.
  inversion H1.
  (* ixc ~ pi_intro *)
  right.
  intros; intro.
  inversion H1.
  (* ixc ~ pi_elim *)
  right.
  intros; intro.
  inversion H1.
  (* ixt cases *)
  right.
  intros; intro.
  inversion H1.
  (* pi_intro cases *)
  right.
  intros.
  intro.
  inversion H1.
  (* pi_elim cases *)
  destruct N.
  (* pi_elim ~ con *)
  right.
  intros; intro.
  inversion H1.
  (* pi_elim ~ ixc *)
  right.
  intros; intro.
  inversion H1.
  (* pi_elim ~ ixt *)
  right.
  intros; intro.
  inversion H1.
  (* pi_elim ~ pi_intro *)
  right.
  intros; intro.
  inversion H1.
  (* pi_elim ~ pi_elim *)
  replace (depth_nte (termstar_nl_pi_elim M1 M2)) with (S (max (depth_nte M1) (depth_nte M2)))
   in H by (cbv;auto).
  apply le_n_0_eq in H.
  inversion H.
  (* step cases *)
  intros.
  destruct M.
  (* con *)
  destruct N.
  assert ({tau | boundsnCon con5 tau sS} +
          {forall tau , ~boundsnCon con5 tau sS}) by (apply boundsnCon_dec).
  assert ({con5 = con0} + {con5 <> con0}) by (apply eq_tcon).
  destruct H1.
  destruct H2.
  left.
  rewrite <- e.
  destruct s.
  exists x.
  apply streq_nl_te_con. 
  assumption.
  assumption.
  right.
  intros.
  intro.
  inversion H1.
  contradiction.
  right.
  intros.
  intro.
  inversion H1.
  apply n0 with tau.
  rewrite H4.
  assumption.
  (* con ~ ixc *)
  right.
  intros; intro.
  inversion H1.
  (* con ~ ixt *)
  right.
  intros; intro.
  inversion H1.
  (* con ~ pi_intro *)
  right.
  intros; intro.
  inversion H1.
  (* con ~ pi_elim *)
  right.
  intros; intro.
  inversion H1.
  (* ixc cases *)
  destruct N.
  right.
  intros; intro.
  inversion H1.
  (* ixc ~ ixc *)
  assert ({ixc = ixc0} + {ixc <> ixc0}) by (apply Nat.eq_dec).
  destruct H1.
  destruct sG.
  (* empty ctx *)
  right.
  intros; intro.
  inversion H1.
  (* nonempty ctx *)
  destruct ixc.
  replace (depth_nte (termstar_nl_ixc 0)) with 0 in H by (cbv; auto).
  rewrite <- e.
  left.
  exists s.
  apply streq_nl_te_var_zero.
  assumption.
  rewrite <- e.
  assert ({tau | streq_nl_te sS sG (termstar_nl_ixc ixc) (termstar_nl_ixc ixc) tau} +
        {forall tau , ~ streq_nl_te sS sG (termstar_nl_ixc ixc) (termstar_nl_ixc ixc) tau}).
  apply IHn.
  assumption.
  replace (depth_nte (termstar_nl_ixc (S ixc))) with (S ixc) in H by (cbv; auto).
  apply le_S_n in H.
  cbv; auto.
  inversion H1.
  left.
  destruct H2.
  exists x.
  apply streq_nl_te_var_succ.
  assumption.
  assumption. 
  right.
  intros; intro.
  inversion H3.
  apply H2 with tau.
  assumption.
  right; intros; intro.
  inversion H1.
  rewrite H2 in H5.
  contradiction.
  rewrite H2 in H3.
  contradiction.
  (* ixc ~ ixt *)
  right.
  intros; intro.
  inversion H1.
  (* ixc ~ pi_intro *)
  right.
  intros; intro.
  inversion H1.
  (* ixc ~ pi_elim *)
  right.
  intros; intro.
  inversion H1.
  (* ixt cases *)
  right.
  intros; intro.
  inversion H1.
  (* pi_intro cases *)
  right.
  intros; intro.
  inversion H1.
  (* pi_elim cases *) 
  destruct N.
  (* pi_elim ~ con *)
  right.
  intros; intro.
  inversion H1.
  (* pi_elim ~ ixc *)
  right.
  intros; intro.
  inversion H1.
  (* pi_elim ~ ixt *)
  right.
  intros; intro.
  inversion H1.
  (* pi_elim ~ pi_intro *)
  right.
  intros; intro.
  inversion H1.
  (* pi_elim ~ pi_elim *)
  assert ({tau | streq_nl_te sS sG M1 N1 tau} +
          {forall tau , ~ streq_nl_te sS sG M1 N1 tau}).  
  apply IHn.
  assumption.
  replace (depth_nte (termstar_nl_pi_elim M1 M2)) with (S (max (depth_nte M1) (depth_nte M2))) in H by (cbv; auto).
  apply le_S_n in H.
  apply le_trans with (Nat.max (depth_nte M1) (depth_nte M2)).
  apply le_max_l.
  assumption.
  destruct H1.
  destruct s.
  destruct x.
  right.
  intros; intro.
  inversion H1.
  assert ( (stype_nl_tcon tcon5) = (stype_nl_pi_intro tau2 tau)).
  eauto using streq_nl_te_strong_determinacy.
  inversion H11.
  assert ({algeq_nl_te sS sG M2 N2 x1} +
          {~ algeq_nl_te sS sG M2 N2 x1}).
  apply algeq_lemma. (* with n (algdepth M2 N2 x1). *)
  (*apply phony.
  reflexivity.*)
  assumption.
  destruct H1.
  left.
  exists x2.
  apply streq_nl_te_pi_elim with x1.
  assumption.
  assumption.
  right.
  intros; intro.
  inversion H1.
  assert ( (stype_nl_pi_intro x1 x2) =  (stype_nl_pi_intro tau2 tau)).
  eauto using streq_nl_te_strong_determinacy.
  inversion H11.
  apply n0.
  rewrite H13; auto.
  right.
  intros; intro.
  inversion H1.
  apply n0 with (stype_nl_pi_intro tau2 tau).
  assumption.
Qed.
*)
  (*
  right.
  intros; intro.
  inversion H1.
  apply n0 with (stype_nl_pi_intro tau2 tau).
  assumption.
*)
  (* Lemma b 


Lemma algeq_nl_te_dec:
  forall (n : nat) (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    algdepth M N tau <= n ->
    wfssig_nl sS ->
    { algeq_nl_te sS sG M N tau } + {~ algeq_nl_te sS sG M N tau}.
Proof. *)

(*
Fixpoint algeq_nl_te_dec' (n m : nat) (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy)
         (streq_lemma : forall (sS : snsgn) (sG : snctx) (M N : nte),
                          wfssig_nl sS -> { tau | streq_nl_te sS sG M N tau } + { forall tau , ~ streq_nl_te sS sG M N tau})
         {struct m}:
    m <= n -> algdepth M N tau = m ->
    wfssig_nl sS ->
    { algeq_nl_te sS sG M N tau } + {~ algeq_nl_te sS sG M N tau}.
  (* Lemma 2 *)
  generalize dependent tau.
  generalize dependent N.
  generalize dependent M.
  generalize dependent sG.
  generalize dependent sS.
  generalize dependent m.
  induction n.
  (* algdepth 0 - only by streq and for tau = a  *)
  intros.
  assert ({tau | streq_nl_te sS sG M N tau} + {forall tau, ~streq_nl_te sS sG M N tau}).
  eauto using streq_lemma.
  destruct H2.
  destruct s.
  assert ({x = tau} + {x <> tau}) by (decide equality; apply eq_con).
  destruct H2.
  rewrite e in s.
  destruct tau.
  (* decide from streq for tau = a *)
  left.
  apply algeq_nl_te_streq.
  assumption.
  (* contradiction from tau = tau1 -> tau2 *)
  apply le_n_0_eq in H.
  rewrite <- H in H0.
  right.
  intro.
  apply algdepth_pi_intro with M N tau1 tau2.
  symmetry.
  assumption.
  (* contradiction on determiancy from x <> tau *)
  right.
  intro.
  inversion H2.
  apply streq_nl_te_determinacy_l with sS sG M N x.
  assumption.
  exists nM'.
  assumption.
  inversion H4.
  apply streq_nl_te_determinacy_r with sS sG M N x.
  assumption.
  exists nN'.
  assumption.
  apply streq_nl_te_determinacy_r with sS sG M N x.
  assumption.
  exists nN'.
  assumption.
  apply streq_nl_te_determinacy_r with sS sG M N x.
  assumption.
  exists nN'.
  assumption.
  apply n.
  apply streq_nl_te_strong_determinacy with sS sG M N.
  assumption.
  rewrite <- H8.
  assumption.
  rewrite <- H10 in H0.
  apply le_n_0_eq in H.
  rewrite <- H in H0.
  apply algdepth_pi_intro with M N tau1 tau2.
  symmetry; assumption.
  (* contradiction from ~streq *)
  right.
  intro.
  apply le_n_0_eq in H.
  rewrite <- H0 in H.
  inversion H2.  
  assert (0 <> algdepth M N tau) by (eauto using algdepth_whr_l).
  contradiction.
  assert (0 <> algdepth M N tau) by (eauto using algdepth_whr_r).
  contradiction.
  apply n with (stype_nl_tcon a).
  assumption.
  rewrite <- H9 in H.
  assert (0 <> algdepth M N (stype_nl_pi_intro tau1 tau2)) by (eauto using algdepth_pi_intro).
  rewrite H10 in H11.
  rewrite <- H9 in H11.
  contradiction.
  (* step case *)
  intros.
  destruct tau.
  (* whr and streq cases *)
  assert ({M'| whr_nl_te M M'} + {forall M', ~ whr_nl_te M M'}) by (apply whr_nl_te_dec). 
  destruct H2.
  destruct s.
  assert ({ algeq_nl_te sS sG x N (stype_nl_tcon tcon5) } + { ~ algeq_nl_te sS sG x N (stype_nl_tcon tcon5)}).
  apply IHn with(algdepth x N (stype_nl_tcon tcon5)) .
  apply le_S_n.
  apply lt_le_trans with (algdepth M N (stype_nl_tcon tcon5)).
  apply algdepth_le_whr_l.
  assumption.
  rewrite H0.
  assumption.
  reflexivity.
  assumption.
  destruct H2.
  (* case whr M and algeq *)
  left.
  apply algeq_nl_te_whr_l with x.
  assumption.
  assumption.
  (* case "possible whr N" *)
  assert ({N'| whr_nl_te N N'} + {forall N', ~ whr_nl_te N N'}) by (apply whr_nl_te_dec).
  destruct H2.
  destruct s.
  assert ({ algeq_nl_te sS sG M x0 (stype_nl_tcon tcon5) } + { ~ algeq_nl_te sS sG M x0 (stype_nl_tcon tcon5)}). 
  apply IHn with (algdepth M x0 (stype_nl_tcon tcon5)).
  apply le_S_n.
  apply lt_le_trans with (algdepth M N (stype_nl_tcon tcon5)).
  apply algdepth_le_whr_r.
  assumption.
  rewrite H0.
  assumption.
  reflexivity.
  assumption.
  destruct H2.
  (* case whr N and algeq *)
  left.
  apply algeq_nl_te_whr_r with x0.
  assumption.
  assumption.
  (* neither whr M nor whr N *)
  right.
  intro.
  inversion H2.
  (* contradiction on whr M *)
  assert (nM' = x) by (eauto using whr_nl_te_determinacy).
  apply n0.
  rewrite <- H10.
  assumption.
  (* contradiction on whr N *)
  assert (nN' = x0) by (eauto using whr_nl_te_determinacy).
  apply n1.
  rewrite <- H10.
  assumption.
  (* contradiction on streq for tcon *)
  eapply streq_nl_te_determinacy_l with sS sG M N (stype_nl_tcon tcon5).
  assumption.
  exists x.
  assumption.
  (* whr M and ~algeq and ~whr N *)
  right.
  intro.
  inversion H2.
  assert (x = nM') by (eauto using whr_nl_te_determinacy).
  apply n0.
  rewrite H10.
  assumption.
  apply n1 with nN'.
  assumption.
  (* contradiction on whr M and streq *)  
  apply streq_nl_te_determinacy_l with sS sG M N (stype_nl_tcon tcon5).
  assumption.
  exists x.
  assumption.
  (* case ~ whr M *)
  assert ({N'| whr_nl_te N N'} + {forall N', ~ whr_nl_te N N'}) by (apply whr_nl_te_dec).
  destruct H2.
  destruct s.
  assert ({ algeq_nl_te sS sG M x (stype_nl_tcon tcon5)} + { ~ algeq_nl_te sS sG M x (stype_nl_tcon tcon5)}).
  apply IHn with(algdepth M x (stype_nl_tcon tcon5)).
  apply le_S_n.
  apply lt_le_trans with (algdepth M N (stype_nl_tcon tcon5)).
  apply algdepth_le_whr_r.
  assumption.
  rewrite H0.
  assumption.
  reflexivity.
  assumption.
  destruct H2.
  (* decide by whr N and algeq *)
  left.
  apply algeq_nl_te_whr_r with x.
  assumption.
  assumption. 
  (* ~ whr M and whr N and and ~algeq *)
  right.
  intro.
  inversion H2.
  (* contradiction on whr M *)
  apply n0 with nM'.
  assumption.
  assert (x = nN').
  apply whr_nl_te_determinacy with N.
  assumption.
  assumption.
  rewrite <- H10 in H9.
  contradiction.
  (* whr M and streq *)
  eapply streq_nl_te_determinacy_r with sS sG M N (stype_nl_tcon tcon5).
  assumption.
  exists x.
  assumption.
  (* neither whr M nor whr N on tcon hence streq *)
  assert ({tau | streq_nl_te sS sG M N tau} + {forall tau, ~ streq_nl_te sS sG M N tau})  
    by (apply streq_lemma; assumption). (* with (depth_nte M);  auto with arith).*)
  destruct H2.
  destruct s.
  assert ({x = (stype_nl_tcon tcon5)} + { x <> (stype_nl_tcon tcon5)}) by (decide equality; apply eq_con).
  destruct H2.
  (* decide from streq *)
  left.
  apply algeq_nl_te_streq.
  rewrite <- e.
  assumption.
  (* contradiction from determinacy of streq *)
  right.
  intro.
  inversion H2.
  apply n0 with nM'.
  assumption.
  apply n1 with nN'.
  assumption.
  assert (x =  stype_nl_tcon tcon5).
  eauto using (streq_nl_te_strong_determinacy).
  contradiction.
  (* contradiction from all *)
  right.
  intro.
  inversion H2.
  apply n0 with nM'; auto.
  apply n1 with nN'; auto.
  apply n2 with  (stype_nl_tcon tcon5); auto.
  (* algeq step *)
  assert ({ M' | cs_nte M M'}).
  apply cs_nte_dec.
  assert ({ N' | cs_nte N N'}).
  apply cs_nte_dec.
  destruct H2.
  destruct H3.
  assert ({algeq_nl_te sS (tau1 :: sG) (termstar_nl_pi_elim x (termstar_nl_ixc 0)) (termstar_nl_pi_elim x0 (termstar_nl_ixc 0)) tau2} +
         {~algeq_nl_te sS (tau1 :: sG) (termstar_nl_pi_elim x (termstar_nl_ixc 0)) (termstar_nl_pi_elim x0 (termstar_nl_ixc 0)) tau2}).
  apply IHn with (algdepth (termstar_nl_pi_elim x (termstar_nl_ixc 0)) (termstar_nl_pi_elim x0 (termstar_nl_ixc 0)) (tau2)).
  apply le_S_n.
  apply lt_le_trans with ( (algdepth M N (stype_nl_pi_intro tau1 tau2))).
  apply algdepth_pi_elim; assumption.
  rewrite H0.
  assumption.
  reflexivity.
  assumption.
  destruct H2.
  (* decide for eta expansion *)
  left.
  apply algeq_nl_te_eta_exp with x x0.
  assumption.
  assumption.
  assumption.
  (* propagate negation *)
  right.
  intro.
  apply n0.
  inversion H2.
  assert (x = nM').
  apply cs_nte_determinacy with M.
  auto.
  auto.
  rewrite H12.
  assert (x0 = nN').
  apply cs_nte_determinacy with N.
  auto.
  auto.
  rewrite H13.
  assumption.
Qed.


Lemma streq_nl_te_dec:
  forall (sS : snsgn) (sG : snctx) (M N : nte),
    wfssig_nl sS ->
    { tau | streq_nl_te sS sG M N tau } + { forall tau , ~ streq_nl_te sS sG M N tau}
with algeq_nl_te_dec:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    wfssig_nl sS ->
    { algeq_nl_te sS sG M N tau } + {~ algeq_nl_te sS sG M N tau}.
Proof.
  intros.
  apply streq_nl_te_dec' with (depth_nte M).
  assumption.
  auto with arith.
  assumption.
  (* lemma 2 *)
  intros.
  apply algeq_nl_te_dec' with (algdepth M N tau) (algdepth M N tau).
  assumption.
  auto with arith.
  reflexivity.
  assumption.
Qed.

STOP.
*)

(*     
Lemma eq_nTy':
  forall (m n : nat) (sS : snsgn) (sG : snctx) (A1 A2 : nTy) (kappa : snK),
    n <= m -> n = depth_nTy A1 ->
    wfssig_nl sS ->
    ( walgeq_nl_Ty sS sG A1 A2 kappa )
      \/ ~ (walgeq_nl_Ty sS sG A1 A2 kappa).
Proof.(*
  induction m.
  intros.
  destruct A1.
  destruct A2.
  assert ({boundsnTCon tcon5 kappa sS} +
          {~boundsnTCon tcon5 kappa sS}) by (apply boundsnTCon_dec).
  assert ({tcon5 = tcon0} + {tcon5 <> tcon0}) by (apply eq_tcon).
  destruct H2.
  destruct H3.
  rewrite <- e.
  left.
  apply walgeq_nl_Ty_refl.
  assumption.
  assumption.
  right.
  intros.
  intro.
  inversion H2.
  contradiction.
  right.
  intros.
  intro.
  inversion H2.
  apply n0.
  rewrite H5.
  assumption.
  (* tcon ~ pi_intro *)
  right.
  intros.
  intro.
  inversion H2.
  (* tcon ~ pi_elim *)
  right.
  intros.
  intro.
  inversion H2.
  (* pi_intro and pi_intro at 0 *)
  replace (depth_nTy (typestar_nl_pi_intro A1_1 A1_2))
      with (S (max (depth_nTy A1_1) (depth_nTy A1_2))) in H0 by (cbv; auto).
  rewrite H0 in H.
  inversion H.
  (* pi_elim ~ pi_elim at 0 *)
  replace (depth_nTy (typestar_nl_pi_elim A1 nte5))
      with (S (depth_nTy A1)) in H0 by (cbv; auto).
  rewrite H0 in H.
  inversion H.
  (* STEP case *)
  intros.
  destruct A1.
  destruct A2.
  assert ({tcon0 = tcon5} + {tcon0 <> tcon5}) by (apply eq_tcon).
  assert ({boundsnTCon tcon5 kappa sS}
          + {~boundsnTCon tcon5 kappa sS}) by (apply boundsnTCon_dec).
  destruct H2.
  destruct H3.
  left.
  rewrite e.
  auto using walgeq_nl_Ty_refl.
  right.
  intros.
  intro.
  inversion H2.
  rewrite <- H4 in H8.
  apply n0.
  assumption.
  right.
  intros.
  intro.  
  inversion H2.
  symmetry in H5; contradiction.
  right.
  intros.
  intro.
  inversion H2.  
  right.
  intros.
  intro.
  inversion H2.
  destruct A2.
  right.
  intros.
  intro.
  inversion H2.
  (* pi_intro ~ pi_intro at S n *)  
  replace (depth_nTy (typestar_nl_pi_intro A1_1 A1_2))
    with (S (max (depth_nTy A1_1) (depth_nTy A1_2))) in H0 by (cbv; auto).
  remember (depth_nTy A1_1).
  remember (depth_nTy A1_2).
  assert ((exists A1_2',  cstu_nTy A1_2 A1_2') \/ (forall A1_2' , ~cstu_nTy A1_2 A1_2')).
  apply cstu_nTy_dec.
  assert ((exists A2_2',  cstu_nTy A2_2 A2_2') \/ (forall A2_2' , ~cstu_nTy A2_2 A2_2')).
  apply cstu_nTy_dec.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  assert ((walgeq_nl_Ty sS sG A1_1 A2_1 kappa) \/
           ~ walgeq_nl_Ty sS sG A1_1 A2_1 kappa).
  apply IHm with n0.
  apply lt_n_Sm_le.
  apply lt_le_trans with n.
  rewrite H0.
  apply le_lt_n_Sm.
  apply le_max_l.
  assumption.
  assumption.
  assumption.
  assert ((walgeq_nl_Ty sS (erasure_Ty A1_1 :: sG) x x0 kappa) \/
           ~ walgeq_nl_Ty sS (erasure_Ty A1_1 :: sG) x x0 kappa).
  apply IHm with n1.
  apply lt_n_Sm_le.
  apply lt_le_trans with n.
  rewrite H0.
  apply le_lt_n_Sm.
  apply le_max_r.
  assumption.
  apply cstu_nTy_depth with A1_2.
  assumption.
  assumption.
  assumption.
  (* we have both IH now ... *)
  destruct H4.
  destruct H5.
  destruct kappa.  
  left.
  apply walgeq_nl_Ty_pi_intro with x x0.
  assumption.
  assumption.
  assumption.
  assumption.
  right.
  intros.
  intro.
  inversion H6.
  right.
  intro.
  inversion H6.
  assert (nA2' = x).
  apply cstu_nTy_determinacy with A1_2.
  assumption.
  assumption.
  rewrite H18 in H17.
  assert (nB2' = x0).
  apply cstu_nTy_determiancy with A2_2.
  assumption.
  assumption.
  rewrite H19 in H17.
  rewrite <- H15 in H5.
  contradiction.
  (* next case *)
  right.
  intros.
  intro.
  inversion H6.
  rewrite <- H15 in H4.
  contradiction.
  (* not cstu *)
  right.
  intros.
  intro.
  inversion H4.
  apply H3 with nB2'.
  assumption.
  (* not cstu - symmetric case *)
  right.
  intros.
  intro.
  inversion H4.
  apply H2 with nA2'.
  assumption.
  (* pi_elim ~ pi_intro *)
  right.
  intros.
  intro.
  inversion H2.
  (* _ ~ pi elim *)
  destruct A2.
  right.
  intros.
  intro.
  inversion H2.
  right.
  intros.
  intro.
  inversion H2.
  (* pi_elim ~ pi_elim *)
  assert ((exists tau, algeq_nl_te sS sG nte5 nte0 tau) \/ (forall tau , ~ algeq_nl_te sS sG nte5 nte0 tau)).
  admit.
  destruct H2.
  destruct H2. 
  assert (walgeq_nl_Ty sS sG A1 A2 (skind_nl_pi_intro x kappa)
          \/ ~ walgeq_nl_Ty sS sG A1 A2 (skind_nl_pi_intro x kappa)).
  replace (depth_nTy (typestar_nl_pi_elim A1 nte5)) with (S (depth_nTy A1)) in H0 by (cbv; auto).
  destruct n.
  inversion H0.
  apply IHm with n.
  auto with arith.
  auto with arith.
  assumption.
  destruct H3.
  left.
  apply walgeq_nl_Ty_pi_elim with x.
  assumption.
  assumption.
  right.
  intro.
  inversion H4.
  admit. (* x = tau *)
  right.
  intro.
  inversion H3.
  apply H2 with tau.
  assumption.
Admitted.
*)
*)

Lemma walgeq_nTy_determinacy:
  forall (sS : snsgn) (sG : snctx) (A1 A2 : nTy) (kappa : snK),
    { walgeq_nl_Ty sS sG A1 A2 kappa } +
    { ~ (walgeq_nl_Ty sS sG A1 A2 kappa) }.
Proof.
(*
  intros.
  eauto using eq_nTy'.
Qed.
 *)
Admitted.


Lemma walgeq_nTy_dec:
  forall (sS : snsgn) (sG : snctx) (A1 A2 : nTy),
    ( {kappa | walgeq_nl_Ty sS sG A1 A2 kappa} +
      { forall kappa , ~ (walgeq_nl_Ty sS sG A1 A2 kappa)}).
Proof.
Admitted.

  
(*
Lemma eq_nK:    
  forall (sS : snsgn) (sG : snctx) (L1 L2 : nK),
    wfssig_nl sS ->
    ( algeq_nl_K sS sG L1 L2 ) \/ (~ (algeq_nl_K sS sG L1 L2)).
Proof.
  intros.
  remember (depth_K(L1)).
  generalize dependent L2.
  generalize dependent L1.
  generalize dependent sG.
  induction n.
  intros.
  destruct L1.
  destruct L2.
  (* case type ~ type *)
  left.
  apply algeq_nl_K_type.
  assumption.
  (* case type ~ pi_intro *)
  right.
  intro.
  inversion H0.
  inversion Heqn.
  (* case S n *)
  intros.
  destruct L1.
  destruct L2.
  inversion Heqn.
  right.
  intro.
  inversion H0.
  inversion Heqn; clear Heqn.
  (* case S n *)
  destruct L2.
  right.
  intro.
  inversion H0.
  (* step case pi_intro ~ pi_intro *)
  assert (( exists L' , cstu_nK L1 L' )
          \/ (forall L',  ~ (cstu_nK L1 L'))) by (apply cstu_nK_dec).
  assert (( exists L' , cstu_nK L2 L'  )
          \/ (forall L',  ~ (cstu_nK L2 L'))) by (apply cstu_nK_dec).
  inversion H0.
  destruct H3.
  inversion H2.
  destruct H4.
  assert (( algeq_nl_K sS (erasure_Ty nTy5 :: sG) x x0 )
          \/ (~ (algeq_nl_K sS (erasure_Ty nTy5 :: sG) x x0))).
  apply IHn.
  apply cstu_K_depth with L1; assumption. 
  assert (( walgeq_nl_Ty sS sG nTy5 nTy0 skind_nl_type )
          \/ (~ (walgeq_nl_Ty sS sG nTy5 nTy0 skind_nl_type))).
  eauto using eq_nTy.
  destruct H5.
  destruct H6.
  left.
  apply algeq_nl_K_pi_intro with x x0. 
  assumption.
  assumption.
  assumption.  
  assumption.
  right.
  intro.
  apply H6.
  inversion H7.
  assumption.
  right.
  intro.
  apply H5.
  inversion H7.
  assert (x = nK').
  apply cstu_nK_determiancy with L1; assumption.
  rewrite H18.
  assert (x0 = nL').
  apply cstu_nK_determinacy with L2; assumption.
  rewrite H19.
  assumption.
  right.
  intro.
  inversion H5.
  apply H4 with nL'.
  assumption.
  right.
  intro.
  inversion H4.
  apply H3 with nK'.
  assumption.
Qed.  
*)  

  
(*
Lemma wftype_nl_transport_l:
  forall (S : nsgn) (G' : nctx) (A' : nTy) (L' : nK),
    wftype_nl S G' A' L' ->
    forall (G : nctx) (A : nTy) (L : nK),
      cs_nctx G G' ->
      cs_nTy A A' ->
      wftype_nl S G A L.    
  
Lemma wftype_nl_transport:
  forall (S : nsgn) (G : nctx) (A B : nTy) (L1 L2 : nK),
    wftype_nl S G A L1 ->
    wftype_nl S G B L2 ->
    forall (G' : nctx) (A' B' : nTy) (L1' : nK),
      cs_nctx (B :: G) (B' :: G') ->
      cstu_nTy A 0 A' ->
      cs_nK L1 L1' ->
      wftype_nl S (B :: G') A' L1'.
*)
(*  

wftype_nl S G A2 L1
cstu_nTy A 0 A' L1
-> 
intros.
  generalize dependent A'.
  generalize dependent G'.
  generalize dependent L'.
  induction H.
  (* tcon *)
  intros.
  inversion H3.
  constructor.
  admit.
  admit.
  (* pi intro *)
  intros.
  inversion H5.
  inversion H3.
  inversion H0.
  assert ({ G'' | cs_nctx (nA' :: G') G''}) by (apply cs_nctx_dec).
  assert ({nB'' : nTy | cstu_nTy nB'0 (S ixc) nB''}) by (apply cstu_nTy_dec).
  destruct H17.
  destruct H18.
  eapply ty_nl_pi_intro.  
  eapply IHwftype_nl1.
  constructor.
  assumption.
  assumption.
  exact c.
  exact c0.
  apply IHwftype_nl2.
  constructor.
  inversion c.
  rewrite <- H15.
  apply cs_nctx_var.
  assert (nctx'0 = G').
  eapply cs_nctx_determinacy.
  exact H14.
  exact H4.
  rewrite H22.
  exact H19.
  assert (nA'0 = nA').
  eapply cs_nTy_determinacy.
  exact H16.
  assumption.
  rewrite H22.
  assumption.

  eapply cs_nTy_cstu.

  exact H10.
  exact H1.
  exact c0.

  (* pi elim *)
  intros.
  inversion H5.
  assert ({nB'' : nTy | cs_nTy nB' nB''}) by (apply cs_nTy_dec).
  assert ({nB''1 : nTy | cs_nTy nB nB''1}) by (apply cs_nTy_dec).
  assert ({nL' : nK | cs_nK nL nL'}) by (apply cs_nK_dec).
  destruct H11.
  destruct H12.
  destruct H13.
  apply ty_nl_pi_elim with x x1 x0.
  apply IHwftype_nl.
  constructor.
  exact c.
  exact c1.
  exact H4.
  exact H8.
  admit. (* mutual lemma *)
  assert (erasure_ctx nctx5 = erasure_ctx G') by (apply eq_nctx_cs_erasure; auto).
  rewrite <- H11.
  eapply walgeq_nTy_cs; eauto.
  admit.
*)

(** 
    context shifting preservers well-formedness of context

    proof by induction on length of the context

 **)

Lemma wfctx_nl_cs:
  forall (S : nsgn) (G G' : nctx) (A : nTy),
    wfctx_nl S G ->
    cs_nctx G 0 A G' ->
    wftype_nl S G A kindstar_nl_type ->
    wfctx_nl S G'.
Proof.
  intros S [ | G ].
  - intros.
    inversion H0.
    econstructor; eauto.
    + constructor.
  - intros.
    inversion H0.
    econstructor; eauto.
    + constructor; eauto using cu_nTy_inverse_cs, cu_nctx_inverse_cs.
Qed.

        
(**
    * determinacy of wftype
**)

Lemma wftype_nl_determinacy:
  forall (S : nsgn) (G : nctx) (sA : sTy) (A : nTy) (L1 L2 : nK),
    sA = struct_nTy A ->
    wfsig_nl S -> wfctx_nl S G ->
    wftype_nl S G A L1 ->
    wftype_nl S G A L2 ->
    L1 = L2.
Proof.
  intros S G sA A L1 L2 Hstruct HwfS.
  generalize dependent L1.
  generalize dependent L2.
  generalize dependent G.
  generalize dependent A.
  induction sA;
    intros A Hstruct G L1 L2 Hwfctx HwfTy1 HwfTy2.
  -  (* leaf *)      
    inversion HwfTy1.
    + rewrite <- H3 in HwfTy2; inversion HwfTy2.
      eauto using boundnTCon_determinacy.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
  -  (* pi intro *)
    inversion HwfTy1.
    + rewrite <- H3 in Hstruct; inversion Hstruct.
    + rewrite <- H5 in HwfTy2; inversion HwfTy2.
      auto.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
  - (* elim *)
    inversion HwfTy1.
    + rewrite <- H3 in Hstruct; inversion Hstruct.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
      rewrite <- H5 in HwfTy2; inversion HwfTy2.
      assert ((kindstar_nl_pi_intro nB' nL)
              = (kindstar_nl_pi_intro nB'0 nL0))
        by (eauto using IHsA).
      inversion H18.
      rewrite <- H21 in H17.
      eauto using tuts_nK_determinacy.
Qed.  

Lemma wfterm_nl_determinacy:
  forall (S : nsgn) (G : nctx) (sM : ste) (M : nte) (A1 A2 : nTy),
    wfsig_nl S -> wfctx_nl S G ->
    sM = struct_nte M ->
    wfterm_nl S G M A1 ->
    wfterm_nl S G M A2 ->
    A1 = A2.
Proof.
  intros.
  generalize dependent A2.
  generalize dependent A1.
  generalize dependent M.
  generalize dependent G.
  induction sM.
  intros.
  - destruct M as [ c | | | | ] ; inversion H1.
    + inversion H2.
      inversion H3.
      eauto using boundnCon_determinacy.
    + clear H1.
      generalize dependent G.
      generalize dependent A1.
      generalize dependent A2.
      induction ixc.
      * intros.
        inversion H2.
        inversion H3.
        rewrite <- H9 in H5; inversion H5.
        eauto using eq_trans.
      * intros.
        inversion H2.
        rewrite <- H7 in H3.
        inversion H3.
        rewrite <- H7 in H0.
        inversion H0.
        assert (nctx' = nctx'0 /\ nB' = nB'0)
          by (eauto using cu_nctx_determinacy).
        inversion H24.
        assert (nctx'1 = nctx'0)
          by (eapply cu_nctx_determinacy; eauto).
        assert (nA = nA0).
        (* rewrite H19 in H5. *)
        eapply IHixc. 
        rewrite H27 in H22.
        exact H22.
        rewrite <- H25.
        exact H5.
        exact H15.
        rewrite <- H28 in H17.
        eauto using cs_nTy_determinacy, eq_trans.
    + inversion H2.
  - intros.
    destruct M; inversion H1.

    inversion H2.
    inversion H3.

    assert (nctx' = nctx'0) by (eauto using cs_nctx_determinacy).
    rewrite <- H26 in H23.
    assert (nM2' = nM2'0) by (eauto using cstu_nte_determinacy).

    
    assert (nA2 = nA3).
    eapply IHsM.
    rewrite <- H26 in H19.
    eapply wfctx_nl_cs; eauto.
    rewrite H6.
    eapply struct_nte_cstu; eauto.
    rewrite H27 in H13.
    exact H13.
    exact H23.

    rewrite <- H28 in H25.
    f_equal; eauto using cuts_nTy_determinacy.
  - intros.
    destruct M; inversion H1.

    inversion H2.
    inversion H3.
    
    assert (nA2 = nA3).
    eapply IHsM2; eauto.
    rewrite <- H24 in H23.
    eapply tuts_nTy_determinacy; eauto.
Qed.      
  

(**
    * wftype and wfterm decidability 
**)

Fixpoint wftype_nl_dec (S : nsgn) (G : nctx)
         (sA : sTy) (A : nTy) {struct sA}:
    wfsig_nl S -> wfctx_nl S G ->
    sA = struct_nTy A ->
    { L | wftype_nl S G A L } +
    { forall L, ~ (wftype_nl S G A L)}
with wfterm_nl_dec (S : nsgn) (G : nctx)
                   (sM : ste) (M : nte) {struct sM}:
    wfsig_nl S -> wfctx_nl S G ->
    sM = struct_nte M ->
    { A | wfterm_nl S G M A } +
    { forall A, ~ (wfterm_nl S G M A)}.
Proof.
  intros.
  generalize dependent A.
  generalize dependent G.
  induction sA.
  - (* struct ~ leaf *)
    intros.
    destruct A.
    + (* tcon *)
      assert ({ L | boundnTCon tcon5 L S } +
              { forall L, ~ (boundnTCon tcon5 L S)})
        by (apply boundnTCon_dec).
      destruct H2 as [ [L] | contra ].
      * (* boundnTCcon *)
        left; eexists; econstructor; eauto.
      * (* ~ not boundnTCon *)
          right; intros; intro Hwf; inversion Hwf.
          eapply contra; eauto.
    + (* pi intro on leaf *)
      inversion H1.
    + (* pi elim on leaf *)
      inversion H1.
  - (* struct step case pi_intro *)
  intros.
  destruct A.
  +  inversion H1.
  +  inversion H1.
     assert ({L | wftype_nl S G A1 L}
          + {forall L, ~ wftype_nl S G A1 L}).
     apply IHsA1.
     exact H0.
     exact H3.
     destruct H2 as [ [L] | contra ].
     * (* exists L *)
       assert ({L = kindstar_nl_type} + {L <> kindstar_nl_type})
         by (apply eq_nK).
     destruct H2.
     { (* L = type *)
       rewrite e in w.
       assert ({ G' | cs_nctx G 0 A1 G'})
         by (apply cs_nctx_dec; auto with arith).
       destruct H2 as [?G'].
       assert ({ A2' | cstu_nTy A2 0 A2'}) by (apply cstu_nTy_dec).
       destruct H2 as [ ?A2' ].
       assert ({L | wftype_nl S G' A2' L}
               + {forall L, ~ wftype_nl S G' A2' L}).
       {
         apply IHsA2.
         eapply wfctx_nl_cs; eauto.
         rewrite H4.
         eapply struct_nTy_cstu; eauto.
       }
       destruct H2 as [ [L2] | ].
       { 
         assert ({L2 = kindstar_nl_type} +
                 {L2 <> kindstar_nl_type}) by (apply eq_nK).
         destruct H2.
         { (* the valid subcase *)
           left.
           rewrite e0 in w0.
           eexists; econstructor; eauto.
         }
         {  (* L2 <> typeK case *)
           right; intros; intro HwfA2; inversion HwfA2.
           assert (A2' = nB') by (eapply cstu_nTy_determinacy; eauto).
           rewrite <- H13 in H12.
           assert (G' = nctx') by (eapply cs_nctx_determinacy; eauto).
           rewrite <- H14 in H12.
           
           assert (struct_nTy A2 = struct_nTy A2')
             by (eapply struct_nTy_cstu; eauto).
           rewrite H15 in H4.
           
           assert (L2 = kindstar_nl_type).
           eapply wftype_nl_determinacy.
           eauto.
           eauto.
           eapply wfctx_nl_cs. 
           exact H0.
           exact c.
           exact H6.
           exact w0.
           exact H12.
           apply n; auto.
         }
       }
       { (*  ~ wftype_nl S x0 x1 L *)
         right; intros; intro.
         inversion H2.
         eapply n.
         assert (A2' = nB') by (eapply cstu_nTy_determinacy; eauto).
         rewrite H14.
         assert (G' = nctx') by (eapply cs_nctx_determinacy; eauto).
         rewrite H15.
         eauto.
       }
     }
     { (* x <> type *)
       right; intros; intro.
       inversion H2.
       assert (L = kindstar_nl_type)
         by (clear H4; eapply wftype_nl_determinacy; eauto).
       apply n; auto.
     }
     * (* pi intro *)
       inversion H1.
       right; intros; intro.
       inversion H2.
       eapply contra; eauto.
  + inversion H1.
  - (* step case: pi elim *)
    intros.
    destruct A.
    + inversion H1.
    + inversion H1.
    + inversion H1.
      
      assert ( {L : nK | wftype_nl S G A L} +
           {(forall L : nK, ~ wftype_nl S G A L)}).
      apply IHsA; auto.
      destruct H2.
      * destruct s.
        destruct x.
        { (* case : wrong kind of A *)
          right; intros; intro.
          inversion H2.
          assert ( kindstar_nl_type =  (kindstar_nl_pi_intro nB' nL)).
          eapply wftype_nl_determinacy ; eauto.
          inversion H14. }
        { assert ({B : nTy | wfterm_nl S G nte5 B } +
                  {(forall B : nTy, ~ wfterm_nl S G nte5 B )}).
          
          eapply wfterm_nl_dec with (sM := ste5).
          auto.
          auto.
          exact H4.
          
          destruct H2.
          { destruct s.
            assert ({x' | tuts_nK x nte5 x'}) by (apply tuts_nK_dec).
            destruct H2.

(*            assert ({kappa |  walgeq_nl_Ty
                                (erasure_nsgn S) (erasure_nctx G)
                                x0 nTy5 kappa } +
                    { forall kappa , ~ walgeq_nl_Ty
                                (erasure_nsgn S) (erasure_nctx G)
                                x0 nTy5 kappa }).
            apply walgeq_nTy_dec.
 *)
            assert ({walgeq_nl_Ty
                       (erasure_nsgn S) (erasure_nctx G)
                       x0 nTy5 skind_nl_type } +
                    { ~ walgeq_nl_Ty
                        (erasure_nsgn S) (erasure_nctx G)
                        x0 nTy5 skind_nl_type }).
            apply walgeq_nTy_determinacy.
            destruct H2.
            left; exists x1.
            eapply ty_nl_pi_elim.
            exact w.
            exact w0.
            exact w1.
            exact t.

            right.
            intros; intro.
            inversion H2.
            assert (x0 = nB) by (eauto using wfterm_nl_determinacy).
            rewrite H14 in n.
            assert (kindstar_nl_pi_intro nTy5 x =
                    kindstar_nl_pi_intro nB' nL)
              by (eauto using wftype_nl_determinacy).
            inversion H15.
            rewrite H17 in n.
            eapply n; eauto.
          }
          { (* not wf B *)
            right; intros; intro.
            inversion H2.
            eapply n; eauto. } }
      * (* not wf A *)
        right; intros; intro.
        inversion H2.
        eapply n; eauto.

  (* mutual lemma *)

  - generalize dependent M. 
    generalize dependent G.
    induction sM.

    + (* leaf *)
      intros.
      destruct M as [ c | | | | ].
      * (* con *)
        assert ({ A | boundnCon c A S} + {forall A, ~ boundnCon c A S})
               by (apply boundnCon_dec).
        destruct H2.
        { destruct s as [ A' ].
          left; eexists; constructor; eauto. }
        { right; intros; intro; eapply n.
          inversion H2; eauto. }
      * (* ixc *)
        clear H1.
        generalize dependent G.
        induction ixc.
        { intros.
          destruct G.
          { right; intros; intro.
            inversion H1. }
          { left; eexists; econstructor; eauto. } }
        { destruct G.
          { right; intros; intro.
            inversion H1. }
          { intros.            
            assert ({ G'B' | cu_nctx (n :: G) 0 (fst G'B') (snd G'B')} +
                    {forall B' G', ~ cu_nctx (n :: G) 0 G' B'})
              by (apply cu_nctx_dec).
            destruct H1 as [ [[?G' ?B']] | ].
            - cbn in c.
              assert (wfctx_nl S G').
              inversion H0.
              assert (nctx' = G').
              eapply cu_nctx_determinacy; eauto.
              rewrite <- H7; auto.
              assert ({A : nTy | wfterm_nl S G' (termstar_nl_ixc ixc) A} +
                      {(forall A : nTy, ~ wfterm_nl S G' (termstar_nl_ixc ixc) A)})
                by (apply IHixc; auto).

              destruct H2 as [ [ A ] | ].
              + assert ({A' | cs_nTy A 0 A'}) by (apply cs_nTy_dec).
                destruct H2 as [ A' ].
                left; eexists.
                econstructor; eauto.
              + right; intros; intro.
                inversion H2.
                assert (nctx' = G').
                eapply cu_nctx_determinacy; eauto.
                rewrite H11 in H8.
                eapply n0; eauto.
            - right; intros; intro.
              inversion H1.
              eapply n0; eauto. } }
      * (* case ixt - not a w.f. term *)
        right; intro; intro.
        inversion H2.
      * inversion H1.
      * inversion H1.
    + intros.
      destruct M as [ | | | B M | ].
      * inversion H1.
      * inversion H1.
      * inversion H1.
      * inversion H1.
        assert ({L : nK | wftype_nl S G B L} +
                {(forall L : nK, ~ wftype_nl S G B L)}).
             
        eapply wftype_nl_dec with (sA := sTy5).
        auto.
        auto.
        auto.
        
        destruct H2 as [ [L] | ].
        assert ({L = kindstar_nl_type} + {L <> kindstar_nl_type})
          by (apply eq_nK).
        destruct H2.
        rewrite e in w.
        assert ({G' | cs_nctx G 0 B G'})
          by (apply cs_nctx_dec; auto with arith).
        destruct H2 as [G'].
        assert (wfctx_nl S G').
        { destruct G'.
          inversion c.
          econstructor; eauto using cu_nctx_inverse_cs. }
        assert ({M' | cstu_nte M 0 M'}) by (apply cstu_nte_dec).
        destruct H5 as [ M' ].
        assert ({A : nTy | wfterm_nl S G' M' A} +
                {(forall A : nTy, ~ wfterm_nl S G' M' A)}).
        { apply IHsM; auto.
          rewrite H4; eauto using struct_nte_cstu. }
        destruct H5 as [ [A] | ].

        { assert ({A' | cuts_nTy A A'}) as [ A']
            by (apply cuts_nTy_dec).
          left.
          eexists.
          econstructor; eauto. }
        { right; intros; intro.
          inversion H5.
          assert (M' = nM2') by (eauto using cstu_nte_determinacy).
          rewrite <- H16 in  H13.
          assert (nctx' = G') by (eauto using cs_nctx_determinacy).
          rewrite H17 in H13.
          eapply n; eauto. }

        { right; intros; intro.
          inversion H2.
          assert (L = kindstar_nl_type).
          eauto using wftype_nl_determinacy.
          contradiction. }
        { right; intros; intro.
          inversion H2.
          eapply n; eauto. }
      * inversion H1.
    + intros.
      destruct M; inversion H1.
      assert ({A | wfterm_nl S G M1 A} + {forall A, ~ wfterm_nl S G M1 A})
        as [ [A] | ]
          by (eauto using IHsM1).
      * destruct A.

        { right; intros; intro.
          inversion H2.
          assert (typestar_nl_tcon tcon5 = typestar_nl_pi_intro nA2' nA1).
          eauto using wfterm_nl_determinacy.
          inversion H14. }
        { assert ({A1' | wfterm_nl S G M2 A1'} +
                  {forall A1', ~ wfterm_nl S G M2 A1'}) as [ [A1'] | ]
              by (eauto using IHsM2).

          assert ({walgeq_nl_Ty (erasure_nsgn S) (erasure_nctx G)
                                A1' A1 skind_nl_type} +
                  {~ (walgeq_nl_Ty (erasure_nsgn S) (erasure_nctx G)
                                   A1' A1 skind_nl_type)}).
          apply walgeq_nTy_determinacy.
          assert ({A1'' | tuts_nTy A1' M2 A1''})
            as [A1''] by (eauto using tuts_nTy_dec).

          destruct H2.
          left; eexists.
          econstructor; eauto.

          right; intros; intro.
          inversion H2.
          eapply n.
          assert (typestar_nl_pi_intro A1 A2
                  = typestar_nl_pi_intro nA2' nA1).
          eauto using wfterm_nl_determinacy.
          inversion H14.

          assert (A1' = nA2) by (eauto using wfterm_nl_determinacy).
          rewrite H15.
          auto.

          right; intros; intro.
          inversion H2.
          eapply n; eauto. }
        { right; intros; intro.
          inversion H2.
          assert (typestar_nl_pi_elim A nte5 =
                  typestar_nl_pi_intro nA2' nA1).
          eauto using wfterm_nl_determinacy.
          inversion H14. }
      * right; intros; intro.
        inversion H2.
        eapply n; eauto.      

Qed.

