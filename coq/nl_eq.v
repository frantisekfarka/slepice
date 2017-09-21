Require Import defns.

Require Import fusion.

Require Import nl_sgn.
Require Import nl_whr.

(**
   * Standard equality
 **)

(** decidability of equality for nameless syntax **)

Lemma eq_nTy_dec:
  forall (A B : nTy),
    {A = B} + {A <> B}
with eq_nte_dec:
  forall (M N : nte),
    {M = N} + {M <> N}.
Proof.
  (* lemma 1 *)
  intros.
  decide equality.
  apply eq_tcon.
  (* lemma 2 *)
  intros.
  decide equality.
  apply eq_con.
  decide equality.
  decide equality.
Qed.

Lemma eq_nK:
  forall (K L : nK),
    {K = L} + {K <> L}.
Proof.
  decide equality.
  apply eq_nTy_dec.
Qed.

(** equality under erasure w.r.t context shifting **)

Lemma eq_nTy_erasure:
  forall (A A' : nTy),
    cs_nTy A A' ->
    (erasure_Ty A) = (erasure_Ty A').
Proof.
  intros.
  induction H; auto.
  cbv; f_equal.
  apply IHcs_nTy1.
  apply IHcs_nTy2.
Qed.

Lemma eq_nctx_cs_erasure:
  forall (G G' : nctx),
    cs_nctx G G' ->
    (erasure_ctx G) = (erasure_ctx G').
Proof.
  intros.
  induction H.
  cbv; auto.
  cbv; f_equal.
  apply eq_nTy_erasure; auto.
  apply IHcs_nctx.
Qed.  

(**
    * Structural and algorithmic equality 

 **)

(** streq and algeq symmetry **)
Lemma streq_nl_te_symmetry:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    ( streq_nl_te sS sG M N tau ) ->
    ( streq_nl_te sS sG N M tau )
with algeq_nl_te_symmetry:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    ( algeq_nl_te sS sG M N tau ) ->
    ( algeq_nl_te sS sG N M tau ).
Proof.
  (* lemma 1 *)
  intros.
  induction H.
  apply streq_nl_te_var_zero; assumption.
  apply streq_nl_te_var_succ; assumption.
  apply streq_nl_te_con; assumption.
  apply streq_nl_te_pi_elim with tau2.
  assumption.
  apply algeq_nl_te_symmetry; assumption.
  (* lemma 2 *)
  intros.
  induction H.
  apply algeq_nl_te_whr_r with nM'; assumption.
  apply algeq_nl_te_whr_l with nN'; assumption.
  apply algeq_nl_te_streq.
  apply streq_nl_te_symmetry; assumption.
  apply algeq_nl_te_eta_exp with nN' nM'; assumption.
Qed.  

(** determinacy of streq **)

Lemma streq_nl_te_determinacy_l:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    ( streq_nl_te sS sG M N tau ) -> ~ (exists M', whr_nl_te M M').
Proof.
  intros.
  induction H.
  intro.
  decompose record H0.
  inversion H1.
  intro.
  decompose record H1.
  inversion H2.
  intro.
  decompose record H1.
  inversion H2.
  intro.
  destruct nM1.
  decompose record H1.
  inversion H2.
  inversion H6.
  decompose record H1.
  inversion H2.
  inversion H6.
  decompose record H1.
  inversion H2.
  inversion H6.
  inversion H.
  apply IHstreq_nl_te.
  decompose record H1.
  inversion H2.
  exists nM'.
  assumption.
Qed.

Lemma streq_nl_te_determinacy_r:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    ( streq_nl_te sS sG M N tau ) -> ~ (exists N', whr_nl_te N N').
Proof.
  intros.
  eauto using streq_nl_te_determinacy_l, streq_nl_te_symmetry.
Qed.  


Lemma streq_nl_te_ixc_determinacy:
  forall (ixc : Ixc) (sS : snsgn) (sG : snctx) (tau : snTy),
  streq_nl_te sS sG (termstar_nl_ixc ixc) (termstar_nl_ixc ixc) tau ->
  forall (tau' : snTy),
    streq_nl_te sS sG (termstar_nl_ixc ixc) (termstar_nl_ixc ixc) tau' ->
    tau = tau'.
Proof.
  intro.
  induction ixc.
  intros.
  inversion H.
  inversion H0.
  rewrite <- H10.
  rewrite <- H6.
  rewrite <- H7 in H3; inversion H3.
  reflexivity.
  (* step *)
  intros.
  inversion H.
  inversion H0.
  apply IHixc with sS snctx5.
  assumption.
  rewrite <- H4 in H10; inversion H10.
  rewrite <- H15.
  assumption.
Qed.

Lemma streq_nl_te_strong_determinacy:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    ( streq_nl_te sS sG M N tau ) ->
    forall tau' , ( streq_nl_te sS sG M N tau' ) ->
    tau = tau'.
Proof.
  intros.
  generalize dependent tau'.
  induction H. 
  intros.
  inversion H0.
  reflexivity.
  (* ixc *)
  intros.
  inversion H1.
  eauto using streq_nl_te_ixc_determinacy.
  (* con *)
  intros.
  inversion H1.
  eauto using boundsnCon_determinacy.
  (* pi_elim *)
  intros.
  inversion H1.
  assert (stype_nl_pi_intro tau2 tau1 = stype_nl_pi_intro tau3 tau').
  apply IHstreq_nl_te.
  assumption.
  inversion H11.
  reflexivity.
Qed.

(** algeq lifts along whr **)

Lemma algeq_nl_te_whr_lift_l:
  forall (sS : snsgn) (sG : snctx) (M M' N : nte) (tau : snTy),
    whr_nl_te M M' ->
    algeq_nl_te sS sG M' N (tau) ->
    algeq_nl_te sS sG M N (tau).
Proof.
  intros.
  generalize dependent M.
  induction H0.
  intros.
  eapply algeq_nl_te_whr_l; eauto.
  intros.
  eapply algeq_nl_te_whr_r; eauto.
  intros.
  eapply algeq_nl_te_whr_l.
  eauto.
  constructor; eauto.
  (* step *)
  intros.
  assert ({csM | cs_nte M csM }) by (apply cs_nte_dec).
  destruct H3.
  eapply algeq_nl_te_eta_exp.
  exact c.
  exact H0.
  apply IHalgeq_nl_te.
  apply whr_nl_te_head.
  eapply whr_nl_te_cs; eauto.  
Qed.  

Lemma algeq_nl_te_whr_lift_r:
  forall (sS : snsgn) (sG : snctx) (M N N': nte) (tau : snTy),
    whr_nl_te N N' ->
    algeq_nl_te sS sG M N' (tau) ->
    algeq_nl_te sS sG M N (tau).
Proof.
  eauto using algeq_nl_te_symmetry, algeq_nl_te_whr_lift_l.
Qed.

(** algeq can be inversed along whr **)

Lemma algeq_nl_te_whr_inversion_l:
  forall (sS : snsgn) (sG : snctx) (M M' N : nte) (tau : snTy),
    whr_nl_te M M' ->
    algeq_nl_te sS sG M N (tau) ->
    algeq_nl_te sS sG M' N (tau).
Proof.
  intros.
  generalize dependent M'.
  induction H0.
  intros.
  assert (M' = nM') by (eauto using whr_nl_te_determinacy).
  rewrite H2.
  assumption.
  intros.
  eapply algeq_nl_te_whr_r; eauto.
  intros.
  apply streq_nl_te_determinacy_l in H.
  destruct H.
  exists M'; eauto.
  (* step *)
  intros.
  assert ({csM' | cs_nte M' csM' }) by (apply cs_nte_dec).
  destruct H3.
  eapply algeq_nl_te_eta_exp.
  exact c.
  exact H0.
  apply IHalgeq_nl_te.
  apply whr_nl_te_head.
  eapply whr_nl_te_cs; eauto.  
Qed.  

Lemma algeq_nl_te_whr_inversion_r:
  forall (sS : snsgn) (sG : snctx) (M N N': nte) (tau : snTy),
    whr_nl_te N N' ->
    algeq_nl_te sS sG M N (tau) ->
    algeq_nl_te sS sG M N' (tau).
Proof.
  eauto using algeq_nl_te_symmetry, algeq_nl_te_whr_inversion_l.
Qed.
