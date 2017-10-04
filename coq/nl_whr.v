Require Import defns.
Require Import nl_fusion.

(**
    * Weak-head reduction
 **)

(** decidability of weak head-reduction **)

Lemma whr_nl_te_dec:
  forall (M : nte),
    {M' | whr_nl_te M M'} + {forall M', ~ whr_nl_te M M'}.
Proof.
  induction M; try solve [ right; intros; intro; inversion H ].
  destruct M1.
  destruct IHM1.
  left.
  destruct s.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  assumption.
  right; intros; intro; inversion H.
  apply n with nM'.
  assumption.
  destruct IHM1.
  left.
  destruct s.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  assumption.
  right; intros; intro; inversion H.
  apply n with nM'.
  assumption.
  destruct IHM1.
  left.
  destruct s.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  assumption.
  right; intros; intro; inversion H.
  apply n with nM'.
  assumption.
  assert ({ N | tuts_nte M1 M2 N }).
  apply tuts_nte_dec.
  destruct H.
  left.
  exists x.
  apply whr_nl_te_subst.
  assumption.
  destruct IHM1.
  left.
  destruct s.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  assumption.
  right; intros; intro; inversion H.
  apply n with nM'.
  assumption.
Qed.  

(** determinacy of weak head-reduction **)

Lemma whr_nl_te_determinacy:
  forall (M M' M'' : nte),
    whr_nl_te M M' ->
    whr_nl_te M M'' ->
    M' = M''.
Proof.
  induction M.
  intros.
  inversion H.
  intros. inversion H.
  intros. inversion H.
  intros. inversion H.
  clear IHM2.
  destruct M1.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply IHM1.
  assumption.
  assumption.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply IHM1.
  assumption.
  assumption.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply IHM1.
  assumption.
  assumption.
  intros.
  inversion H.
  inversion H0.
  apply tuts_nte_determinacy with M1 M2.
  assumption.
  assumption.
  inversion H9.
  inversion H4.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply IHM1.
  assumption.
  assumption.
Qed.

(** context shifting preserves weak head-reduction **)

Lemma whr_nl_te_cs:
  forall (M M' N N' : nte) (i : Ixc),
    whr_nl_te M M' ->
    cs_nte M i N -> cs_nte M' i N' ->
    whr_nl_te N N'.
 Proof.
  intros.
  generalize dependent N'.
  generalize dependent N.
  induction H.
  intros.
  inversion H0.
  inversion H4.
  apply whr_nl_te_subst.
  eapply tuts_nte_cs; eauto.
  (* elim case *)
  intros.
  inversion H0.
  inversion H1.
  assert (nN' = nN'0) by (eapply cs_nte_determinacy; eauto).
  rewrite <- H14.
  apply whr_nl_te_head.
  apply IHwhr_nl_te; auto.
Qed.

(** context shifting preservs weak head-reduction in inverse **)
 
Lemma whr_nl_te_cs_inversion:
  forall (N N' M M'  : nte) (i : Ixc),
    whr_nl_te N N' -> cs_nte M i N -> cs_nte M' i N' ->
    whr_nl_te M M'.
Proof.
  intros.
  generalize dependent M'.
  generalize dependent M.
  induction H.
  intros.
  inversion H0.
  inversion H6.
  eapply whr_nl_te_subst.
  eapply tuts_nte_cs_inverse; eauto.
  (* step *)
  intros.
  inversion H0.

  inversion H1.
  assert (nN0 = nN1) by  (eapply cs_nte_surjectivity; eauto).
  rewrite H14.
  constructor.
  eapply IHwhr_nl_te; eauto.
Qed.  

Lemma whr_nl_te_cs_inversion_flip:
  forall (N N' M M'  : nte) (i : Ixc),
    whr_nl_te N N' -> cs_nte M i N -> whr_nl_te M M' ->
    cs_nte M' i N'.
Proof.
  intros.
  generalize dependent M'.
  generalize dependent M.
  induction H.
  intros.
  inversion H0.
  rewrite <- H4 in H1.
  inversion H6.
  rewrite <- H10 in H1.
  inversion H1.
  
  eapply cs_nte_tuts.

  exact H13.
  exact H7.
  exact H18.
  exact H.
  inversion H17.

  (* step *)
  intros.
  inversion H0.
  rewrite <- H4 in H1.
  inversion H1.

  rewrite <- H8 in H6.
  inversion H6.
  rewrite <- H16 in H.
  inversion H.

  constructor.
  eapply IHwhr_nl_te.
  exact H6.
  exact H11.
  exact H7.
Qed.  

(** 
weak head-reduction can be reconstructed along context shifting
**)
Lemma whr_nl_te_cs_dec_inverse:
    forall (M M' N' : nte) {i : Ixc},
      cs_nte M i M' -> whr_nl_te M' N' ->
      { N : nte | whr_nl_te M N}.
Proof.
  intros.
  generalize dependent M.
  generalize dependent N'.
  induction M'.
  
  intros.
  assert (False).
  inversion H0.
  contradiction.

  intros.
  assert (False).
  inversion H0.
  contradiction.

  intros.
  assert (False).
  inversion H0.
  contradiction.

  intros.
  assert (False).
  inversion H0.
  contradiction.

  intros.
  destruct M.
  assert (False).
  inversion H.
  contradiction.

  assert (False).
  inversion H.
  contradiction.

  assert (False).
  inversion H.
  contradiction.

  assert (False).
  inversion H.
  contradiction.

  destruct M'1.
  assert (False).
  inversion H0.
  inversion H4.
  contradiction.

  assert (False).
  inversion H0.
  inversion H4.
  contradiction.

  assert (False).
  inversion H0.
  inversion H4.
  contradiction.

  destruct M1.
  assert (False).
  inversion H.
  inversion H5.
  contradiction.

  assert (False).
  inversion H.
  inversion H5.
  contradiction.

  assert (False).
  inversion H.
  inversion H5.
  contradiction.
  
  assert ({N' | tuts_nte M1 M2 N' }).
  apply tuts_nte_dec.
  destruct H1.

  exists x.
  apply whr_nl_te_subst.
  exact t.

  assert (False).
  inversion H.
  inversion H5.
  contradiction.

  destruct M1.

  assert (False).
  inversion H.
  inversion H5.
  contradiction.

  assert (False).
  inversion H.
  inversion H5.
  contradiction.

  assert (False).
  inversion H.
  inversion H5.
  contradiction.

  assert (False).
  inversion H.
  inversion H5.
  contradiction.

  destruct N'.
  
  assert (False).
  inversion H0.
  contradiction.

  assert (False).
  inversion H0.
  contradiction.

  assert (False).
  inversion H0.
  contradiction.

  assert (False).
  inversion H0.
  contradiction.
  
  assert ({N'1 | whr_nl_te (termstar_nl_pi_elim M1_1 M1_2) N'1}).
  eapply IHM'1.
  inversion H0.
  exact H2.
  inversion H.
  exact H5.

  destruct H1.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  exact w.
Qed.  
