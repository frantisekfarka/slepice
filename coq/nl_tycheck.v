Load defns.


Lemma boundcon_dec:
  forall (S : nsgn) (c : con),
    {indomnCon c S} + {~(indomnCon c S)}.
Proof.
(*  intros.
  induction S.
  (* nil case *)
  right.
  intro.
  destruct H.
  destruct H.
  destruct H.
  decompose record H.
  apply app_cons_not_nil in H0.
  contradiction.
  (* step case *)
  destruct a.
  (* con subcase *)
  destruct p.
  assert (H : {c = c0} + {c <> c0}).
  apply eq_con.
  destruct H.
  rewrite <- e.
  destruct IHS.
  right.
  intro.
  destruct H0.
  destruct H0.
  *)

Lemma cstu_nTy_dec:
  forall (A : nTy),
    { exists A' , cstu_nTy A A'  }
    + {forall A',  ~ (cstu_nTy A A')}
with cstu_nte_dec:
  forall (M : nte),
    { exists M' , cstu_nte M M'  }
    + {forall M',  ~ (cstu_nte M M')}.
Proof.
  intros.
  induction A.
  left.
  exists (typestar_nl_tcon tcon5).
  trivial using cstu_nTy_tcon.
  destruct IHA1.
  destruct IHA2.
  left.
  destruct e.
  destruct e0.
  exists (typestar_nl_pi_intro x x0).
  auto using cstu_nTy_pi_intro.
  (* next case *)
  right.
  intro.
  intro.
  inversion H.
  apply n with nB'.
  assumption.
  (* next case *)
  right.
  intro.
  intro.
  inversion H.
  apply n with nA'.
  assumption.
  (* next case *)
  destruct IHA.
  assert ({(exists M' : nte, cstu_nte nte5 M')} +
      {(forall M' : nte, ~ cstu_nte nte5 M')}).
  apply cstu_nte_dec.
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (typestar_nl_pi_elim x x0).
  apply cstu_nTy_pi_elim.
  assumption.
  assumption.
  (* the other sub case *)
  right.
  intro.
  intro.
  inversion H.
  apply n with nM'.
  assumption.
  (* really last case :-) *)
  right.
  intro.
  intro.
  inversion H.
  apply n with nA'.
  assumption.
  (* lemma cstu_nte_dec *)
  intros.
  induction M.
  (* case con *)
  left.
  exists (termstar_nl_con con5).
  auto using cstu_nte_con.
  (* case ixc *)
  left.
  exists (termstar_nl_ixc (ixctx_succ ixc)).
  apply cstu_nte_ixc.
  (* case ixt *)
  left.
  destruct ixt.
  exists (termstar_nl_ixc ixctx_zero).
  apply cstu_nte_zerot.
  auto using termstar_nl_ixt.
  exists (termstar_nl_ixt ixt).
  apply cstu_nte_suct.
  (* case pi_intro *)  
  destruct IHM.
  assert ({(exists A' : nTy, cstu_nTy nTy5 A')} +
          {(forall A' : nTy, ~ cstu_nTy nTy5 A')}).
  apply cstu_nTy_dec.
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (termstar_nl_pi_intro x0 x).
  apply cstu_nte_pi_intro.
  assumption.
  assumption.  
  (* subcase ~ nA' *)
  right.
  intro.
  intro.
  inversion H.
  apply n with nA'.
  assumption.
  (* subcase ~ nM' *)
  right.
  intro.
  intro.
  inversion H.
  apply n with nM'.
  assumption.
  (* case pi elim *)
  destruct IHM1.
  destruct IHM2.
  left.
  destruct e.
  destruct e0.
  exists (termstar_nl_pi_elim x x0).
  auto using cstu_nte_pi_elim.
  (* subcase ~M2 *)
  right.
  intro.
  intro.
  inversion H.
  apply n with nN'.
  assumption.
  (* subcase ~M1 *)
  right.
  intro.
  intro.
  inversion H.
  apply n with nM'.
  assumption.
Qed.
  
Lemma cstu_nK_dec:
  forall (L : nK),
    { exists L' , cstu_nK L L'  }
    + {forall L',  ~ (cstu_nK L L')}.
Proof.
  intros.
  induction L.
  left.
  exists kindstar_nl_type.
  apply cstu_K_type.
  (* step case *)
  assert ({(exists A' : nTy, cstu_nTy nTy5 A')} +
          {(forall A' : nTy, ~ cstu_nTy nTy5 A')}).
  apply cstu_nTy_dec.
  destruct IHL.
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (kindstar_nl_pi_intro x0 x).
  apply cstu_K_pi_intro.
  assumption.
  assumption.
  right.
  intro.
  intro.
  inversion H.
  apply n with nA'.
  assumption.
  right.
  intro.
  intro.
  inversion H0.
  apply n with nL'.
  assumption.
Qed.

Lemma cstu_nTy_inj:
  forall (A B1 B2 : nTy),
    cstu_nTy A B1 -> cstu_nTy A B2 ->
    B1 = B2           
with cstu_nte_inj:
  forall (M N1 N2 : nte),
    cstu_nte M N1 -> cstu_nte M N2 ->
    N1 = N2.
Proof.
  intros.
  generalize dependent B2.
  generalize dependent B1.
  induction A.
  intros.
  inversion H.
  inversion H0.
  auto.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply IHA1.
  assumption.
  assumption.
  apply IHA2.
  assumption.
  assumption.
  (* case pi_elim *)
  intros.
  inversion H; inversion H0.
  f_equal.
  apply IHA.
  assumption.
  assumption.
  apply cstu_nte_inj with nte5.
  assumption.
  assumption.
  (* lemma 2 *)
  intros.
  generalize dependent N2.
  generalize dependent N1.











Lemma boundnTCon_dec:
  forall (S : nsgn) (a : tcon),
    { exists L , boundnTCon a L S } +
    { forall L, ~ (boundnTCon a L S)}.
Proof.
  intros.
  induction S.
  (* nil case *)
  right.
  intro.
  intro.
  inversion H.
  decompose record H0.
  apply app_cons_not_nil in H2.
  contradiction.
  (* step case *)
  destruct a0.
  (* subcase con *)
  destruct p.
  destruct IHS.
  left.
  destruct e.
  exists x.
  inversion H.
  decompose record H0.
  exists (inl(c,n) :: x0).
  exists x1.
  split.
  rewrite H2.
  apply app_comm_cons.
  split.
  intro.
  intro.
  apply H1 with nL'.
  inversion H3.
  inversion H5.
  assumption.
  intro.
  apply H4.
  right.
  intro.
  intro.
  inversion H.
  decompose record H0.
  apply n0 with L.
  destruct x.
  inversion H2.
  exists x.
  exists x0.
  split.
  inversion H2.
  reflexivity.
  split.
  intro.
  intro.
  apply H1 with nL'.
  right.
  assumption.
  intro.
  intro.
  apply H4 with nL'.
  assumption.
  (* last case *)
  destruct p.
  assert ({a = t} + {a <> t}) by (apply eq_tcon).
  destruct IHS.
  destruct H.
  rewrite <- e0. clear e0.
  right.
  intro.
  intro.
  destruct H.
  decompose record H.
  destruct e.
  destruct H2.
  decompose record H2.
  rewrite H5 in H1.
  destruct x.
  admit.
  admit.
  admit.
  admit.
Admitted.

Lemma wftype_nl_dec:
  forall (S : nsgn) (G : nctx) (A : nTy),
    wfsig_nl S -> wfctx_nl S G ->
    { exists L , wftype_nl S G A L } +
    { forall L, ~ (wftype_nl S G A L)}.
Proof.
  intros.
  generalize dependent G.
  induction A.
  (* base case tcon *)
  intros.
  assert ({ exists L , boundnTCon tcon5 L S } +
    { forall L, ~ (boundnTCon tcon5 L S)}) by (apply boundnTCon_dec).
  destruct H1.
  left.
  destruct e.
  exists x.
  apply ty_nl_tcon.
  assumption.
  assumption.
  right.
  intro.
  intro.
  inversion H1.
  apply n with L.
  assumption.
  (* step case pi_intro *)
  intros.
  assert ({exists L , wftype_nl S G A1 L}
          + {forall L, ~ wftype_nl S G A1 L}).
  apply IHA1.
  assumption.
  intros.
  assert ({exists L , wftype_nl S G A2 L}
          + {forall L, ~ wftype_nl S G A2 L}).
  apply IHA2.
  assumption.
(*  destruct H1.
  destruct H2.
  left.
  destruct e.
  destruct e0.
  exists (kindstar_nl_type).
  apply ty_nl_pi_intro with G A1.
*)


Lemma shift:
  forall (sS : snsgn) (sG : snctx) (A : nTy) (L1 L2 L1' L2' : nK),
     wfssig_nl sS ->
     cstu_nK L1 L1' -> cstu_nK L2 L2' ->
     algeq_nl_K sS sG (kindstar_nl_pi_intro A L1) (kindstar_nl_pi_intro A L2) ->
     algeq_nl_K sS ((erasure_Ty A) :: sG) L1' L2'.
Proof.
  intros.
  generalize H2; clear H2.
  generalize H1; clear H1.
  generalize H0; clear H0. 
  generalize H; clear H.
  generalize sG; clear sG.
  generalize L2'; clear L2'.
  generalize L2; clear L2.
  generalize L1'; clear L1'.
  generalize A; clear A.  
  induction L1.
  intros.
  inversion H0.
  destruct L2'.
  apply algeq_nl_K_refl.
  assumption.
  inversion H1.
  rewrite <- H6 in H2.
  inversion H2.
  inversion H16.
  rewrite <- H20 in H18.
  inversion H17.
  rewrite <- H23 in H18.
  inversion H18.
  (* step case *)
  admit.
Admitted.


Lemma eq_nK:
  forall (sS : snsgn) (sG : snctx) (L1 L2 : nK),
    wfssig_nl sS ->
    ( algeq_nl_K sS sG L1 L2 ) \/ (~ (algeq_nl_K sS sG L1 L2)).
Proof.
  intros.
  generalize H. clear H.
  generalize dependent sG.
  generalize sS.
  generalize dependent L2. 
  induction L1.
  (* case L1 = type *)
  admit.
  (* subcase L2 = type *)
  (* subcase L2 = pi_intro *)
  (* case L1 = pi_intro type *)
  intros.
  destruct L2.
  right.
  intro.
  inversion H0.
  (* pi_intro pi_intro *)
  assert ({ exists L' , cstu_nK L1 L'  }
          + {forall L',  ~ (cstu_nK L1 L')}) by (apply cstu_nK_dec).
  assert ({ exists L' , cstu_nK L2 L'  }
          + {forall L',  ~ (cstu_nK L2 L')}) by (apply cstu_nK_dec).
  assert ({ walgeq_nl_Ty sS0 sG nTy5 nTy0 skind_nl_type }
          + {~ (walgeq_nl_Ty sS sG nTy5 nTy5 skind_nl_type)}).
  admit.
  inversion H0.
  decompose record H3.
  inversion H1.
  decompose record H5.
  assert (( algeq_nl_K sS0 (erasure_Ty nTy5 :: sG) x x0 )
          \/ (~ (algeq_nl_K sS0 (erasure_Ty nTy5 :: sG) x x0))).
  admit.
  destruct H2.
  destruct H7.
  left.
  apply algeq_nl_K_pi_intro with x x0. 
  assumption.
  assumption.
  assumption.  
  assumption.
  right.
  intro.
  apply H2.
  inversion H7.
  admit.
  inversion H7.


  
Lemma eq_nTy:
  forall (sS : snsgn) (sG : snctx) (kappa : snK) (A B : nTy),
    { walgeq_nl_Ty sS sG A B kappa } + {~ (walgeq_nl_Ty sS sG A B kappa)}.
Proof.
  intros.



  
  
Lemma tycheck_dec:
  forall (S : nsgn) (G : nctx) (M : nte),
    {exists (A : nTy),  wfterm_nl S G M A
    (forall (A : nTy), ~(wfterm_nl S G M A)).
Proof.
  intros.
  generalize dependent G.
  (* by induction on structure of the term *)
  induction M.
  