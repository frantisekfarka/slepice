Require Import List.

Require Import defns.

Require Import nl_fusion.
Require Import nl_eq.
Require Import nl_sgn.
Require Import nl_whr.


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
  intros sS sG M N tau H.
  induction H.
  - intro Hc.
    decompose record Hc.
    inversion H0.
  - intro Hc.
    decompose record Hc.
    inversion H1.
  - intro Hc.
    decompose record Hc.
    inversion H1.
  - intro.
    destruct nM1.
    + decompose record H1.
      inversion H2.
      inversion H6.
    + decompose record H1.
      inversion H2.
      inversion H6.
    + decompose record H1.
      inversion H2.
      inversion H6.
    + inversion H.
    + apply IHstreq_nl_te.
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
  forall (ixc ixc': Ixc) (sS : snsgn) (sG : snctx) (tau : snTy),
  streq_nl_te sS sG (termstar_nl_ixc ixc) (termstar_nl_ixc ixc') tau ->
  forall (tau' : snTy),
    streq_nl_te sS sG (termstar_nl_ixc ixc) (termstar_nl_ixc ixc') tau' ->
    tau = tau'.
Proof.
  intro.
  induction ixc; intros ixc' sS sG tau Hstreq1 tau' Hstreq2.
  - inversion Hstreq1 as [ sS' sG' tau0 HwfsS HsS' HsG' | | | ].
    inversion Hstreq2 as [ sS'' sG'' tau1 HwfsS'' HsS'' HsG'' | | | ].
    rewrite <- HsG' in HsG''.
    inversion HsG''.
    eauto using eq_trans.
  - (* step *)
    inversion Hstreq1 as [ sS' sG' tau0 HwfsS HsS' HsG' | | | ].
    inversion Hstreq2 as [ sS'' sG'' tau1 HwfsS'' HsS'' HsG'' | | | ].
    eapply IHixc. 
    eauto.
    rewrite <- H11 in H4; inversion H4.
    rewrite <- H9 in H2; inversion H2.
    eauto.
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

(** streq is preserved along cs **)
(*
Fixpoint streq_nl_te_cs (sS : snsgn) (sG sG' : snctx) (M M' N N' : nte) (tau tau' : snTy) (i : Ixc)
  (H : streq_nl_te sS sG M N tau ) {struct H}:
    cs_nte M i M' -> cs_nte N i N' -> cs_snctx sG i tau' sG' ->    
    ( streq_nl_te sS sG' M' N' tau )
with algeq_nl_te_cs (sS : snsgn) (sG sG' : snctx) (M M' N N' : nte) (tau tau' : snTy) (i : Ixc)
    (H : algeq_nl_te sS sG M N tau ) {struct H}:
    cs_nte M i M' -> cs_nte N i N' -> cs_snctx sG i tau' sG' ->
    ( algeq_nl_te sS sG' M' N' tau ).
Proof.
  intros.
  generalize dependent N'.
  generalize dependent M'.
  generalize dependent i.
  generalize dependent tau'.
  generalize dependent sG'.
  
  induction H.

  intros.
  inversion H0.
  rewrite <- H3 in H1; inversion H1.
  rewrite <- H3 in H2; inversion H2.
  inversion H9; constructor; auto; constructor; auto.
  
  rewrite <- H4 in H1; inversion H1.
  rewrite <- H4 in H2; inversion H2.  
  constructor; auto. 

  (* S ixc *)
  intros.
  inversion H1.
  rewrite <- H4 in H3; inversion H3.
  rewrite <- H4 in H2; inversion H2.

  constructor; auto.
  eapply IHstreq_nl_te.
  exact H10.
  constructor.
  constructor.
   
  rewrite <- H6 in H3; inversion H3.  
  rewrite <- H6 in H2; inversion H2.
  
  constructor; auto.
  eapply IHstreq_nl_te; eauto.

  intros.
  inversion H1.
  inversion H3.
  constructor; auto.

  intros.
  inversion H1.
  inversion H3.
  econstructor.
  eapply IHstreq_nl_te; eauto.
  eapply algeq_nl_te_cs; eauto.

  (* lemma 2 *)
  intros.
  generalize dependent N'.
  generalize dependent M'.
  generalize dependent tau'.
  generalize dependent i.
  generalize dependent sG'.
  induction H.

  intros.
  assert ({nM'' | cs_nte nM' i nM''}) by (eapply cs_nte_dec).
  inversion H4.
  
  eapply algeq_nl_te_whr_l.
  eapply whr_nl_te_cs; eauto.
  eapply IHalgeq_nl_te; eauto.

  intros.
  assert ({nN'' | cs_nte nN' i nN''}) by (eapply cs_nte_dec).
  inversion H4.
  
  eapply algeq_nl_te_whr_r.
  eapply whr_nl_te_cs; eauto.
  eapply IHalgeq_nl_te; eauto.

  intros.
  constructor.
  eapply streq_nl_te_cs; eauto.

  intros.  
  assert ({M'' | cs_nte M' 0 M''}) by (apply cs_nte_dec).
  destruct H5.
  assert ({N'' | cs_nte N' 0 N''}) by (apply cs_nte_dec).
  destruct H5.
 
  econstructor.
  exact c.
  exact c0.

  eapply IHalgeq_nl_te.
  apply cs_snctx_cs; eauto.
  constructor.

  eapply cs_nte_cs.
  exact H3.
  exact c.
  exact H.

  constructor.
  constructor.
  eapply cs_nte_cs.
  exact H4.
  exact c0.
  exact H0.
  constructor.
Qed.
*)

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
  assert ({csM | cs_nte M 0 csM }) by (apply cs_nte_dec).
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
  assert ({csM' | cs_nte M' 0 csM' }) by (apply cs_nte_dec).
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


(**
streq and algeq are preserved by context shiftin inverse 
**)
(*
Fixpoint streq_nl_te_cs_inversion (sS : snsgn) (sG sG' : snctx) (M M' N N' : nte) (tau tau' : snTy)
  (H : streq_nl_te sS sG' M' N' tau ) (i : Ixc) {struct H}:
    cs_nte M i M' -> cs_nte N i N' -> cs_snctx sG i tau' sG' ->    
    ( streq_nl_te sS sG M N tau )
with algeq_nl_te_cs_inversion (sS : snsgn) (sG sG' : snctx) (M M' N N' : nte) (tau tau' : snTy)
    (H : algeq_nl_te sS sG' M' N' tau ) (i : Ixc) {struct H}:
    cs_nte M i M' -> cs_nte N i N' -> cs_snctx sG i tau' sG' ->
    ( algeq_nl_te sS sG M N tau ).
Proof.
  intros.
  generalize dependent N.
  generalize dependent M.
  generalize dependent i. 
  generalize dependent tau'. 
  generalize dependent sG.
  
  induction H.

  intros.
  inversion H0.
  rewrite <- H4 in H1; inversion H1.
  rewrite <- H4 in H2; inversion H2.
  constructor; auto.
  
  intros.
  inversion H1.
  rewrite <- H5 in H3; inversion H3.
  rewrite <- H5 in H2; inversion H2.
  rewrite <- H13 in H0; inversion H0.

  destruct ixc.

  assert (snctx5 = tau'1 :: snctx0).
  apply cs_snctx_zeroc; auto.
  rewrite H14 in H0.
  inversion H0.
  constructor; auto.


  destruct ixc'.
  inversion H0.
  
  constructor; auto.
  eapply IHstreq_nl_te.
  exact H13.
  constructor.
  constructor.
  
  rewrite <- H6 in H3; inversion H3.  
  rewrite <- H6 in H2; inversion H2.
  constructor; auto.
  eapply IHstreq_nl_te; eauto.

  intros.
  inversion H1.
  inversion H3.
  constructor; auto.

  intros.
  inversion H1.
  inversion H3.
  econstructor.
  eapply IHstreq_nl_te; eauto.
  eapply algeq_nl_te_cs_inversion; eauto.

  (* lemma 2 *)
  intros.
  generalize dependent N.
  generalize dependent M.
  (* generalize dependent tau'. *)
  generalize dependent i.
  generalize dependent sG.
  induction H.

  intros.

  assert ({M' | whr_nl_te M M'}).
  eapply whr_nl_te_cs_dec_inverse; eauto.
  destruct H4.
  
  eapply algeq_nl_te_whr_l.
  exact w.
  eapply IHalgeq_nl_te; eauto.
  eapply whr_nl_te_cs_inversion_flip; eauto.

  intros.
  assert ({N' | whr_nl_te N N'}).
  eapply whr_nl_te_cs_dec_inverse; eauto.
  destruct H4.
  
  eapply algeq_nl_te_whr_r.
  exact w.
  eapply IHalgeq_nl_te; eauto.
  eapply whr_nl_te_cs_inversion_flip; eauto.

  intros.
  constructor.
  eapply streq_nl_te_cs_inversion; eauto.

  intros.  
  assert ({M'' | cs_nte M 0 M''}) by (apply cs_nte_dec).
  destruct H5.
  assert ({N'' | cs_nte N 0 N''}) by (apply cs_nte_dec).
  destruct H5.
 
  econstructor.
  exact c.
  exact c0.

  eapply IHalgeq_nl_te.
  apply cs_snctx_cs; eauto.
  constructor.

  eapply cs_nte_cs.
  exact H3.
  exact H.
  exact c.

  constructor.
  constructor.
  eapply cs_nte_cs.
  exact H4.
  exact H0.
  exact c0.
  constructor.
Qed.
*)

(** transformation of streq to algeq  **)
(*
Lemma streq_nl_te_algeq:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    wfssig_nl sS ->
    ( streq_nl_te sS sG M N tau) ->
    ( algeq_nl_te sS sG M N tau).
Proof.
  intros.
  generalize dependent N.
  generalize dependent M.
  generalize dependent sG.
  induction tau.
  intros.
  constructor; auto.

  intros.
  assert ({M' | cs_nte M 0 M'}) by (apply cs_nte_dec).
  destruct H1.
  assert ({N' | cs_nte N 0 N'}) by (apply cs_nte_dec).
  destruct H1.

  econstructor.
  exact c.
  exact c0.
  eapply IHtau2.
  eapply streq_nl_te_pi_elim with (tau2 := tau1).
  eapply streq_nl_te_cs.
  exact H0.
  exact c.
  exact c0.
  eapply cs_snctx_var.
  eapply IHtau1.
  constructor.
  exact H.
Qed.  
*)

(**
* Weak algorithmic equality 
**)

(** walgeq is preserved by context shifting **)
(*
Lemma walgeq_nl_Ty_cs:
  forall (sS : snsgn) (sG sG' : snctx) (A A' B B' : nTy) (tau : snTy) (kappa : snK) (i : Ixc),
    walgeq_nl_Ty sS sG A B kappa ->
    cs_nTy A i A' -> cs_nTy B i B' -> cs_snctx sG i tau sG' ->
    walgeq_nl_Ty sS sG' A' B' kappa.
Proof. 
  intros.
  generalize dependent B'.
  generalize dependent A'.
  generalize dependent sG'.
  generalize dependent tau.
  generalize dependent i.
  induction H.
  - (* tcon *)
    intros.
    inversion H1; inversion H3.
    constructor; auto.
  - (* pi_intro *)
    intros.
    inversion H4; inversion H5.
    assert ({nB'' | cstu_nTy nB' 0 nB''}) by (apply cstu_nTy_dec).
    destruct H18.
    assert ({nB''0 | cstu_nTy nB'0 0 nB''0}) by (apply cstu_nTy_dec).
    destruct H18.
    econstructor.
    eapply IHwalgeq_nl_Ty1; eauto.
    eauto.
    eauto.
    assert (erasure_nTy nA1 = erasure_nTy nA') by (eapply eq_nTy_erasure; eauto).
    rewrite <- H18.
    eapply IHwalgeq_nl_Ty2.
    eapply cs_snctx_var_succ; eauto.
    eapply cs_nTy_cstu.
    exact H11. 
    exact H0.
    exact c.
    eapply cs_nTy_cstu; eauto.
  -  (* pi_elim *)
    intros.
    inversion H1; inversion H3.
    eapply walgeq_nl_Ty_pi_elim.
    eapply IHwalgeq_nl_Ty; eauto.
    eapply algeq_nl_te_cs; eauto.
Qed.
*)


(** decidability for nomalizing terms **)

Lemma algeq_nl_te_decnorm:
  forall (sS : snsgn) (sG : snctx) (M M' N N' : nte) (tau : snTy),
    (algeq_nl_te sS sG M M' tau) ->
    (algeq_nl_te sS sG N N' tau) ->
    (algeq_nl_te sS sG M N tau) \/
    (~ algeq_nl_te sS sG M N tau).
Proof.
  intros sS sG M M' N N' tau H.
  generalize dependent N.
  generalize dependent N'.
  induction H.

  - intros.
    apply IHalgeq_nl_te in H1.

    destruct H1.

    + left.
      econstructor; eauto.

    + right.
      intro.
      apply H1; auto.
      eapply algeq_nl_te_whr_inversion_l; eauto.

  - intros.
    apply IHalgeq_nl_te in H1.

    destruct H1.

    + left.
      assumption.

    + right.
      intro.
      apply H1; auto.

  - intros.

    generalize dependent nM.
    generalize dependent nN.

    induction H0.

    + intros.
      apply IHalgeq_nl_te in H1.
      destruct H1.

      * left.
        eapply algeq_nl_te_whr_r; eauto.

      * right.
        intro.

        apply H1.
        eapply algeq_nl_te_whr_inversion_r; eauto.

    + intros.
      apply IHalgeq_nl_te in H1.
      assumption.

    + intros.

      admit. (* ??? *)

    + intros.
      eapply IHalgeq_nl_te in H2.

      