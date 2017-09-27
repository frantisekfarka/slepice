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
  assert ({ N | tuts_nte M1 M2 N } + {forall N, ~ (tuts_nte M1 M2 N)}).
  apply tuts_nte_dec.
  destruct H.
  left.
  destruct s.
  exists x.
  apply whr_nl_te_subst.
  assumption.
  right; intros; intro; inversion H.
  apply n with M'.
  assumption.
  inversion H3.
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
  forall (M M' N N' : nte),
    whr_nl_te M M' ->
    cs_nte M N -> cs_nte M' N' ->
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
  rewrite <- H12.
  apply whr_nl_te_head.
  apply IHwhr_nl_te; auto.
Qed.

(** context shifting preservs weak head-reduction in inverse **)
 
Lemma whr_nl_te_cs_inversion:
  forall (N N' M M'  : nte),
    whr_nl_te N N' -> cs_nte M N -> cs_nte M' N' ->
    whr_nl_te M M'.
Proof.
  intros.
  generalize dependent M'.
  generalize dependent M.
  induction H.
  intros.
  inversion H0.
  inversion H5.
  apply whr_nl_te_subst.
  eapply tuts_nte_cs_inverse; eauto.
  (* step *)
  intros.
  inversion H0; inversion H1.
  assert (nN0 = nN1) by  (eapply cs_nte_surjectivity; eauto).
  rewrite H12.
  constructor.
  eapply IHwhr_nl_te; eauto.
Qed.  
