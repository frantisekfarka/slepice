Require Import List.
Require Import defns.

Require Import nl_eq.

(**
  * boundnCon
 **)

(** decidability of boundnCon **)

Lemma boundnCon_dec:
  forall (S : nsgn) (c : con),
    { A | boundnCon c A S } +
    { forall A, ~ (boundnCon c A S)}.
Proof.
  induction S; intros.

  - right.
    intros. intro Hc.
    unfold boundnCon in Hc.
    decompose record Hc.
    apply app_cons_not_nil in H.
    contradiction.

  - destruct a.

    + destruct p.

      assert ({c = c0} + {c <> c0}) by (apply eq_con).
      destruct H.

      * subst.
        left.
        exists n.
        exists nil.
        exists S.
        split; auto.

      * destruct IHS with c.
        left.
        destruct s.
        exists x.
        unfold boundnCon in b.
        decompose record b.
        exists (inl (c0, n) :: x0).
        exists x1.
        rewrite H.
        split.
        auto.
        intros.
        intro.
        inversion H0.
        inversion H2.
        apply n0; auto.
        apply H1 with nA'; auto.

        right.
        intros.
        intro.  
        unfold boundnCon in H.
        decompose record H.
        destruct x.
        inversion H0.
        apply n0; auto.
        assert (S = x ++ inl (c, A) :: x0).
        inversion H0.
        auto.
        apply n1 with A.
        rewrite H1.
        exists x.
        exists x0.
        split.
        auto.
        intro.
        intro.
        apply H2 with nA'.
        right.
        assumption.

    +  (* inr cases *)
      destruct IHS with c.
      left.
      destruct s.
      exists x.
      unfold boundnCon in b.
      decompose record b.
      rewrite H.
      exists (inr p :: x0).
      exists x1.
      split.
      auto.
      intros.
      intro.
      apply H1 with nA'.
      inversion H0.
      inversion H2.
      assumption.
      (* not bound at all *)
      right.
      intros.
      intro.
      apply n with A.
      unfold boundnCon in H.
      decompose record H.
      destruct x.
      inversion H0.
      inversion H0.
      exists x.
      exists x0.
      split.
      auto.
      intros.
      intro.
      apply H2 with nA'.
      right.
      assumption.
Qed.  

(** determianacy of boundnCon **)

Lemma boundnCon_weak_r:
  forall (S : nsgn) (c : con) (a : tcon) (A : nTy) (L : nK),
    boundnCon c A (inr (a , L) :: S) ->
    boundnCon c A S.
Proof.
  intros.
  unfold boundnCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  exists x.
  exists x0.
  inversion H0.
  split.
  auto.
  intros.
  intro.
  apply H2 with nA'.
  right.
  assumption.
Qed.  

Lemma boundnCon_weak_l:
  forall (S : nsgn) (c d : con) (A B : nTy),
    boundnCon c A (inl (d , B) :: S) ->
    c <> d ->
    boundnCon c A S.
Proof.
  intros.
  unfold boundnCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  destruct H0.
  symmetry; assumption.
  exists x.
  exists x0.
  inversion H1.
  split.
  auto.
  intros.
  intro.
  apply H3 with nA'.
  right.
  assumption.
Qed.  

Lemma boundnCon_weak_determinacy:
  forall (S : nsgn) (c : con) (A1 A2 : nTy),
    boundnCon c A1 (inl (c, A2) :: S) ->
    ~ indomnCon c S
    -> A1 = A2.
Proof.
  intros.
  unfold boundnCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  reflexivity.
  destruct H0.
  exists A1.
  exists x.
  exists x0.
  split.
  inversion H1.
  reflexivity.
  intros; intro.
  apply H3 with nA'.
  right.
  assumption.
Qed.
    
Lemma boundnCon_determinacy:
  forall (S : nsgn) (c : con) (A1 A2 : nTy),
    wfsig_nl S ->
    boundnCon c A1 S ->
    boundnCon c A2 S ->
    A1 = A2.
Proof.
  intros.
  induction H.
  (* nil case *)
  intros.
  unfold boundnCon in H0.
  decompose record H0.
  apply app_cons_not_nil in H.
  contradiction.
  (* step case *)
  intros.
  apply IHwfsig_nl; eapply boundnCon_weak_r ; eauto.
  (* *)
  assert ({c = c0} + {c <> c0}) by (apply eq_con).
  destruct H4.
  rewrite e in H0.
  rewrite e in H1.
  assert (A1 = nA).
  eauto using boundnCon_weak_determinacy; auto.
  assert (A2 = nA).
  eauto using boundnCon_weak_determinacy; auto.
  rewrite H4.
  rewrite H5.
  reflexivity.
  apply IHwfsig_nl; eauto using boundnCon_weak_l; auto.
Qed.

(**
  * boundsnCon
 **)

(** decidability of boundsnCon **)

Lemma boundsnCon_dec:
  forall (sS :snsgn) (c : con),
    { tau | boundsnCon c tau sS } +
    { forall tau, ~boundsnCon c tau sS }.
Proof.
  intros.
  induction sS.
  right.
  intros.
  intro.
  unfold boundsnCon in H.
  decompose record H.
  apply app_cons_not_nil in H0.
  contradiction.
  destruct a.
  destruct p.
  assert ({c = c0} + {c <> c0}) by (apply eq_con).
  destruct H.
  rewrite e.
  left.
  exists s.
  exists nil.
  exists sS.
  split.
  auto.
  intros.
  intro.
  inversion H.
  destruct IHsS.
  left.
  destruct s0.
  exists x.
  unfold boundsnCon in b.
  decompose record b.
  exists (inl (c0, s) :: x0).
  exists x1.
  rewrite H.
  split.
  auto.
  intros.
  intro.
  inversion H0.
  inversion H2.
  apply n; auto.
  apply H1 with tau'; auto.
  right.
  intros.
  intro.  
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  apply n; auto.
  assert (sS = x ++ inl (c, tau) :: x0).
  inversion H0.
  auto.
  apply n0 with tau.
  rewrite H1.
  exists x.
  exists x0.
  split.
  auto.
  intro.
  intro.
  apply H2 with tau'.
  right.
  assumption.
  (* inr cases *)
  destruct IHsS.
  left.
  destruct s.
  exists x.
  unfold boundsnCon in b.
  decompose record b.
  rewrite H.
  exists (inr p :: x0).
  exists x1.
  split.
  auto.
  intros.
  intro.
  apply H1 with tau'.
  inversion H0.
  inversion H2.
  assumption.
  (* not bound at all *)
  right.
  intros.
  intro.
  apply n with tau.
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  inversion H0.
  exists x.
  exists x0.
  split.
  auto.
  intros.
  intro.
  apply H2 with tau'.
  right.
  assumption.
Qed.  

(** determianacy of boundsnCon **)

Lemma boundsnCon_weak_r:
  forall (sS : snsgn) (c : con) (a : tcon) (tau : snTy) (kappa : snK),
    boundsnCon c tau (inr (a , kappa) :: sS) ->
    boundsnCon c tau sS.
Proof.
  intros.
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  exists x.
  exists x0.
  inversion H0.
  split.
  auto.
  intros.
  intro.
  apply H2 with tau'.
  right.
  assumption.
Qed.  

Lemma boundsnCon_weak_l:
  forall (sS : snsgn) (c d : con) (tau1 tau2 : snTy),
    boundsnCon c tau1 (inl (d , tau2) :: sS) ->
    c <> d ->
    boundsnCon c tau1 sS.
Proof.
  intros.
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  destruct H0.
  symmetry; assumption.
  exists x.
  exists x0.
  inversion H1.
  split.
  auto.
  intros.
  intro.
  apply H3 with tau'.
  right.
  assumption.
Qed.  

Lemma boundsnCon_weak_determinacy:
  forall (sS : snsgn) (c : con) (tau1 tau2 : snTy),
    boundsnCon c tau1 (inl (c, tau2) :: sS) ->
    ~ indomsnCon c sS
    -> tau1 = tau2.
Proof.
  intros.
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  reflexivity.
  destruct H0.
  exists tau1.
  exists x.
  exists x0.
  split.
  inversion H1.
  reflexivity.
  intros; intro.
  apply H3 with tau'.
  right.
  assumption.
Qed.

Lemma boundsnCon_determinacy:
  forall (sS : snsgn) (a : tcon) (tau1 tau2 : snTy),
    wfssig_nl sS ->
    boundsnCon a tau1 sS ->
    boundsnCon a tau2 sS ->
    tau1 = tau2.
Proof.
  intros.
  induction H.
  (* nil case *)
  intros.
  unfold boundsnCon in H0.
  decompose record H0.
  apply app_cons_not_nil in H.
  contradiction.
  (* step case *)
  intros.
  apply IHwfssig_nl; eapply boundsnCon_weak_r ; eauto.
  (* *)
  assert ({c = a} + {c <> a}) by (apply eq_con).
  destruct H3.
  rewrite <- e in H0.
  rewrite <- e in H1.
  assert (tau1 = tau).
  eauto using boundsnCon_weak_determinacy; auto.
  assert (tau2 = tau).
  eauto using boundsnCon_weak_determinacy; auto.
  rewrite H3.
  rewrite H4.
  reflexivity.
  apply IHwfssig_nl; eauto using boundsnCon_weak_l; auto.
Qed.

(**
  * boundnTCon
 **)

(** decidability of boundnTCon **)

Lemma boundnTCon_dec:
  forall (S : nsgn) (a : tcon),
    { L | boundnTCon a L S } +
    { forall L, ~ (boundnTCon a L S)}.
Proof.
  intros.
  induction S.
  right.
  intros.
  intro.
  unfold boundnTCon in H.
  decompose record H.
  apply app_cons_not_nil in H0.
  contradiction.
  destruct a0.
  (* inl - inr case *)
  destruct IHS.
  left.
  destruct s.
  exists x.
  unfold boundnTCon in b.
  decompose record b.
  rewrite H.
  exists (inl p :: x0).
  exists x1.
  split.
  auto.
  intros.
  intro.
  apply H1 with nL'.
  inversion H0.
  inversion H2.
  assumption.
  (* not bound at all *)
  right.
  intros.
  intro.
  apply n with L.
  unfold boundnTCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  inversion H0.
  exists x.
  exists x0.
  split.
  auto.
  intros.
  intro.
  apply H2 with nL'.
  right.
  assumption. 
  (* inr - inr case *)
  destruct p.
  assert ({t = a} + {t <> a}) by (apply eq_tcon).
  destruct H.
  rewrite e.
  left.
  exists n.
  exists nil.
  exists S.
  split.
  auto.
  intros.
  intro.
  inversion H.
  destruct IHS.
  left.
  destruct s.
  exists x.
  unfold boundnTCon in b.
  decompose record b.
  exists (inr (t, n) :: x0).
  exists x1.
  rewrite H.
  split.
  auto.
  intros.
  intro.
  inversion H0.
  inversion H2.
  apply n0; auto.
  apply H1 with nL'; auto.
  right.
  intros.
  intro.  
  unfold boundnTCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  apply n0; auto.
  assert (S = x ++ inr (a, L) :: x0).
  inversion H0.
  auto.
  apply n1 with L.
  rewrite H1.
  exists x.
  exists x0.
  split.
  auto.
  intro.
  intro.
  apply H2 with nL'.
  right.
  assumption.
Qed.  

(** determianacy of boundnTCon **)

Lemma boundnTCon_weak_l:
  forall (S : nsgn) (c : tcon) (a : tcon) (A : nTy) (L : nK),
    boundnTCon a L (inl (c , A) :: S) ->
    boundnTCon a L S.
Proof.
  intros.
  unfold boundnTCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  exists x.
  exists x0.
  inversion H0.
  split.
  auto.
  intros.
  intro.
  apply H2 with nL'.
  right.
  assumption.
Qed.  

Lemma boundnTCon_weak_r:
  forall (S : nsgn) (a b : tcon) (L K : nK),
    boundnTCon a L (inr (b , K) :: S) ->
    a <> b ->
    boundnTCon a L S.
Proof.
  intros.
  unfold boundnTCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  destruct H0.
  symmetry; assumption.
  exists x.
  exists x0.
  inversion H1.
  split.
  auto.
  intros.
  intro.
  apply H3 with nL'.
  right.
  assumption.
Qed.  

Lemma boundnTCon_weak_determinacy:
  forall (S : nsgn) (a : tcon) (L1 L2 : nK),
    boundnTCon a L1 (inr (a, L2) :: S) ->
    ~ indomnTCon a S
    -> L1 = L2.
Proof.
  intros.
  unfold boundnTCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  reflexivity.
  destruct H0.
  exists L1.
  exists x.
  exists x0.
  split.
  inversion H1.
  reflexivity.
  intros; intro.
  apply H3 with nL'.
  right.
  assumption.
Qed.
  
Lemma boundnTCon_determinacy:
  forall (S : nsgn) (a : tcon) (L1 L2 : nK),
    wfsig_nl S ->
    boundnTCon a L1 S ->
    boundnTCon a L2 S ->
    L1 = L2.
Proof.
  intros.
  induction H.
  (* nil case *)
  intros.
  unfold boundnTCon in H0.
  decompose record H0.
  apply app_cons_not_nil in H.
  contradiction.
  (* step case *)
  intros.
  (* *)
  assert ({a = a0} + {a <> a0}) by (apply eq_tcon).
  destruct H4.
  rewrite e in H0.
  rewrite e in H1.
  assert (L1 = nL).
  eauto using boundnTCon_weak_determinacy; auto.
  assert (L2 = nL).
  eauto using boundnTCon_weak_determinacy; auto.
  rewrite H4.
  rewrite H5.
  reflexivity.
  (* *)
  eauto using boundnTCon_weak_r; auto.
  apply IHwfsig_nl; eauto using boundnTCon_weak_l.  
Qed.

(**
  * boundsnTCon
 **)

(** decidability of boundsnTCon **)

Lemma boundsnTCon_dec:
  forall (sS : snsgn) (a : tcon),
    {kappa | boundsnTCon a kappa sS} + {forall kappa , ~ boundsnTCon a kappa sS}.
Proof.
  intros.
  induction sS.
  right.
  intros.
  intro.
  unfold boundsnTCon in H.
  decompose record H.
  apply app_cons_not_nil in H0.
  contradiction.
  destruct a0.
  (* inl cases *)
  destruct IHsS.
  left.
  destruct s.
  exists x.
  unfold boundsnTCon in b.
  decompose record b.
  rewrite H.
  exists (inl p :: x0).
  exists x1.
  split.
  auto.
  intros.
  intro.
  apply H1 with kappa'.
  inversion H0.
  inversion H2.
  assumption.
  (* not bound at all *)
  right.
  intros.
  intro.
  apply n with kappa.
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  inversion H0.
  exists x.
  exists x0.
  split.
  auto.
  intros.
  intro.
  apply H2 with kappa'.
  right.
  assumption.
  (* int cases *)  
  destruct p.
  assert ({a = t} + {a <> t}) by (apply eq_con).
  destruct H.
  rewrite e.
  left.
  exists s.
  exists nil.
  exists sS.
  split.
  auto.
  intros.
  intro.
  inversion H.
  destruct IHsS.
  left.
  destruct s0.
  exists x.
  unfold boundsnTCon in b.
  decompose record b.
  exists (inr (t, s) :: x0).
  exists x1.
  rewrite H.
  split.
  auto.
  intros.
  intro.
  inversion H0.
  inversion H2.
  apply n; auto.
  apply H1 with kappa'; auto.
  right.
  intros.
  intro.  
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  apply n; auto.
  assert (sS = x ++ inr (a, kappa) :: x0).
  inversion H0.
  auto.
  apply n0 with kappa.
  rewrite H1.
  exists x.
  exists x0.
  split.
  auto.
  intro.
  intro.
  apply H2 with kappa'.
  right.
  assumption.
Qed.
  
(** determianacy of boundsnTCon **)

Lemma boundsnTCon_weak_l:
  forall (sS : snsgn) (c : con) (a : tcon) (tau : snTy) (kappa : snK),
    boundsnTCon a kappa (inl (c , tau) :: sS) ->
    boundsnTCon a kappa sS.
Proof.
  intros.
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  exists x.
  exists x0.
  inversion H0.
  split.
  auto.
  intros.
  intro.
  apply H2 with kappa'.
  right.
  assumption.
Qed.  

Lemma boundsnTCon_weak_r:
  forall (sS : snsgn) (a b : tcon) (kappa1 kappa2 : snK),
    boundsnTCon a kappa1 (inr (b , kappa2) :: sS) ->
    a <> b ->
    boundsnTCon a kappa1 sS.
Proof.
  intros.
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  destruct H0.
  symmetry; assumption.
  exists x.
  exists x0.
  inversion H1.
  split.
  auto.
  intros.
  intro.
  apply H3 with kappa'.
  right.
  assumption.
Qed.  

Lemma boundsnTCon_weak_determinacy:
  forall (sS : snsgn) (a : tcon) (kappa1 kappa2 : snK),
    boundsnTCon a kappa1 (inr (a, kappa2) :: sS) ->
    ~ indomsnTCon a sS
    -> kappa1 = kappa2.
Proof.
  intros.
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  reflexivity.
  destruct H0.
  exists kappa1.
  exists x.
  exists x0.
  split.
  inversion H1.
  reflexivity.
  intros; intro.
  apply H3 with kappa'.
  right.
  assumption.
Qed.
  
Lemma boundsnTCon_determinacy:
  forall (sS : snsgn) (a : tcon) (kappa1 kappa2 : snK),
    wfssig_nl sS ->
    boundsnTCon a kappa1 sS ->
    boundsnTCon a kappa2 sS ->
    kappa1 = kappa2.
Proof.
  intros.
  induction H.
  (* nil case *)
  intros.
  unfold boundsnTCon in H0.
  decompose record H0.
  apply app_cons_not_nil in H.
  contradiction.
  (* step case *)
  intros.
  (* *)
  assert ({a = a0} + {a <> a0}) by (apply eq_tcon).
  destruct H3.
  rewrite e in H0.
  rewrite e in H1.
  assert (kappa1 = kappa).
  eauto using boundsnTCon_weak_determinacy; auto.
  assert (kappa2 = kappa).
  eauto using boundsnTCon_weak_determinacy; auto.
  rewrite H3.
  rewrite H4.
  reflexivity.
  (* *)
  eauto using boundsnTCon_weak_r; auto.
  apply IHwfssig_nl; eauto using boundsnTCon_weak_l.  
Qed.


(**  checking of boundsnTcon **)

Lemma boundsnTCon_check:
  forall (sS : snsgn) (a : tcon) (kappa : snK),
    wfssig_nl sS ->
    {boundsnTCon a kappa sS} + {~ boundsnTCon a kappa sS}.
Proof.
  intros.
  assert ({ kappa' | boundsnTCon a kappa' sS} +
          { forall kappa', ~ boundsnTCon a kappa' sS})
    as [ [kappa'] | ]
      by (apply boundsnTCon_dec).
  - assert ({kappa = kappa'} + {kappa <> kappa'})
      as [ eq_kappa | ]
        by ( apply eq_snK).
    + (* kappa = kappa' *)
      rewrite eq_kappa.
      left; auto.
    + (* kappa <> kappa' *)
      right; intro Hb.
      assert (kappa = kappa')
        by (eauto using boundsnTCon_determinacy).
      contradiction.
  - right; intro.
    eapply n; eauto.
Qed.

(*  
(** erausre stability for TCon **)
Lemma indomsnTCon_stable:
  forall (S : nsgn) (a : tcon),
    indomsnTCon a (erasure_nsgn S) ->
    indomnTCon a S.
Proof.
  
  intros S a.

  induction S.

  - intro H.
    unfold indomsnTCon in H.
    unfold boundsnTCon in H.
    decompose record H.
    cbn in H1.
    apply app_cons_not_nil in H1.
    contradiction.

  - destruct a0.
    destruct p.
    cbn.

    intro H.

    assert (indomnTCon a S).
    apply IHS.
    
    unfold indomsnTCon.
    unfold boundsnTCon.
    unfold indomsnTCon in H.
    unfold boundsnTCon in H.

    decompose record H.
    exists x.

    destruct x0.
    cbn in H1; inversion H1.

    exists x0.
    exists x1.

    cbn in H1.
    inversion H1.
    split; auto.
    intros; intro.
    eapply H2.
    right; eauto.

    unfold indomnTCon in H0.
    unfold boundnTCon in H0.
    decompose record H0.

    unfold indomnTCon.
    unfold boundnTCon.
    exists x.
    exists (inl (c, n) :: x0).
    exists x1.
    split.
    cbn.
    f_equal; auto.

    intros; intro.
    eapply H3.
    destruct H1.
    inversion e.
    eauto.

    destruct p.
    cbn.

    assert ({t = a} + {t <> a}) as [ | ] by (apply eq_tcon).

    + rewrite e.
      intros.
      unfold indomnTCon.
      unfold boundnTCon.

      exists n.
      exists nil.
      exists S.
      split.
      cbn; auto.
      intros; intro.
      inversion H0.

    + intros.
      assert (indomnTCon a S).
      apply IHS.

      unfold indomsnTCon in H.
      unfold boundsnTCon in H.
      decompose record H.

      destruct x0.
      cbn in H1.
      inversion H1.
      contradiction.

      unfold indomsnTCon.
      unfold boundsnTCon.
      exists x. 
      exists x0.
      exists x1.

      split.
      cbn in H1.
      inversion H1.
      auto.

      intros; intro.
      eapply H2.
      right; eauto.

      unfold indomnTCon in H0.
      unfold boundnTCon in H0.
      decompose record H0.

      unfold indomnTCon.
      unfold boundnTCon.
      exists x.
      exists (inr (t, n) :: x0).
      exists (x1).
      split.
      cbn.
      f_equal; auto.
      intros; intro.
      eapply H3.
      destruct H1.
      inversion e; contradiction.
      eauto.
Qed.

(** * Stability if indomsnCon and indomsnTCon * **)
  
(** erausre stability for con **)
Lemma indomsnCon_stable:
  forall (S : nsgn) (c : con),
    indomsnCon c (erasure_nsgn S) ->
    indomnCon c S.
Proof. 
  intros S a; 
  unfold indomsnCon;
  unfold boundsnCon;
  unfold indomnCon;
  unfold boundnCon.
  induction S.
  
  - intro H.
    decompose record H.
    cbn in H1.
    apply app_cons_not_nil in H1.
    contradiction.

  - destruct a0; destruct p;
    cbn.

    + assert ({c = a} + {c <> a}) as [ | ] by (apply eq_con).
    
      * rewrite e.
        intros.
        
        exists n.
        exists nil.
        exists S.
        split.
        cbn; auto.
        intros; intro.
        inversion H0.

      * intros.
        assert (indomnCon a S).
        
        { apply IHS.
          decompose record H.

          destruct x0.
          cbn in H1.
          inversion H1.
          contradiction.

          exists x. 
          exists x0.
          exists x1.

          split.
          cbn in H1.
          inversion H1.
          auto. 

          intros; intro.
          eapply H2.
          right; eauto. }

      unfold indomnCon in H0.
      unfold boundnCon in H0.
      decompose record H0.

      exists x.
      exists (inl (c, n) :: x0).
      exists (x1).
      split.
      cbn.
      f_equal; auto.
      intros; intro.
      eapply H3.
      destruct H1.
      inversion e; contradiction.
      eauto.

    + 
    intro H.
    decompose record H.

    assert (indomnCon a S).
    { apply IHS.   
      
      exists x.
      destruct x0.
      cbn in H1; inversion H1.

      exists x0.
      exists x1.

      cbn in H1.
      inversion H1.
      split; auto.
      intros; intro.
      eapply H2.
      right; eauto. }

    unfold indomnCon in H0.
    unfold boundnCon in H0.
    decompose record H0.

    exists x2.
    exists (inr (t, n) :: x3).
    exists x4.
    split.
    cbn.
    f_equal; auto.

    intros; intro.
    eapply H5.
    destruct H3.
    inversion e.
    eauto.
Qed.

*)
     