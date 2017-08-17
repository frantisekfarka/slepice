Require Import List.
Require Import Arith.Max.
Require Import Arith.Lt.

Require Import defns.
Require Import fusion.


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


Lemma boundnTCon_dec:
  forall (S : nsgn) (a : tcon),
    ( exists L , boundnTCon a L S ) \/
    ( forall L, ~ (boundnTCon a L S)).
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
  destruct H.
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
  apply H with L.
  unfold boundnTCon in H0.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct x.
  inversion H0.
  exists x.
  exists x0.
  split.
  inversion H0.
  reflexivity.
  split.
  intro.
  intro.
  apply H1 with nL'.
  right.
  assumption.
  intro.
  intro.
  apply H2 with nL'.
  assumption.
  (* last case *)
  destruct p.
  assert ({a = t} + {a <> t}) by (apply eq_tcon).
  destruct IHS.
  destruct H.
  (* a in head *)
  rewrite <- e; clear e.
  right.
  intro.
  intro.
  destruct H; destruct H; destruct H; destruct H1.
  destruct H0; destruct H0; destruct H0.  
  destruct x.
  inversion H.
  destruct H0.
  apply H2 with x1.
  rewrite <- H5.
  rewrite H0.
  clear H5 H4 H2 H1 H H0 H3.
  induction x2.
  left.
  reflexivity.
  right.
  apply IHx2.
  inversion H.
  rewrite <- H4 in H1.
  apply H1 with n.
  left.
  reflexivity.
  (* a <> t *)
  left.
  destruct H0.
  exists x.
  destruct H.
  destruct H.
  exists (inr (t, n) :: x0).
  exists x1.
  destruct H.
  destruct H0.
  split.  
  rewrite H.
  auto.
  split.
  intro.
  intro.
  apply H0 with nL'.
  destruct H2.
  inversion H2.
  rewrite H4 in n0.
  contradiction.
  assumption.
  assumption.
  assert (~ boundnTCon a n S).
  apply H0.
  admit.
Admitted.


Lemma boundsnTCon_dec:
  forall (sS : snsgn) (a : tcon) (kappa : snK),
    {boundsnTCon a kappa sS} + {~ boundsnTCon a kappa sS}.
Proof.
Admitted.

(** depth auxiliaries *)

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
  | (termstar_nl_ixc ixc) => 0
  | (termstar_nl_ixt ixt) => 0
  | (termstar_nl_pi_intro A M) => S (depth_nte M)
  | (termstar_nl_pi_elim M N) => S (max (depth_nte M) (depth_nte N))
end.


Lemma whr_nl_te_dec:
  forall (M : nte),
    (exists M', whr_nl_te M M') \/ (forall M', ~ whr_nl_te M M').
Proof.
  induction M.
  right.
  intros; intro.
  inversion H.
  right.
  intros; intro.
  inversion H.
  right.
  intros; intro.
  inversion H.
  right.
  intros; intro.
  inversion H.
  destruct M1.
  destruct IHM1.
  left.
  destruct H.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  assumption.
  right.
  intros.
  intro.
  inversion H0.
  apply H with nM'.
  assumption.
  destruct IHM1.
  left.
  destruct H.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  assumption.
  right.
  intros.
  intro.
  inversion H0.
  apply H with nM'.
  assumption.
  destruct IHM1.
  left.
  destruct H.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  assumption.
  right.
  intros.
  intro.
  inversion H0.
  apply H with nM'.
  assumption.
  assert (( exists N , tuts_nte M1 M2 N ) \/ (forall N, ~ (tuts_nte M1 M2 N))).
  apply tuts_nte_dec.
  destruct H.
  left.
  destruct H.
  exists x.
  apply whr_nl_te_subst.
  assumption.
  inversion IHM1.
  left.
  inversion H0.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  assumption.
  right.
  intros; intro.
  inversion H1.
  apply H with M'.
  assumption.
  apply H0 with nM'.
  assumption.
  destruct IHM1.
  destruct H.
  left.
  exists (termstar_nl_pi_elim x M2).
  apply whr_nl_te_head.
  assumption.
  right.
  intros. intro.
  inversion H0.
  apply H with nM'.
  assumption.
Qed.  

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
  apply tuts_nte_inj with M1 M2.
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

Lemma streq_nl_te_determinacy:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    ( streq_nl_te sS sG M N tau ) -> ~ (exists M', whr_nl_te M M').
Proof.
  induction M.
  intros.
  intro.
  destruct H0.
  inversion H0.
  intros.
  intro.
  destruct H0.
  inversion H0.
  intros.
  intro.
  destruct H0.
  inversion H0.
  intros.
  intro.
  destruct H0.
  inversion H0.
  (* step case *)
  destruct M1.
  intros.
  intro.
  inversion H0.
  inversion H1.
  inversion H.
  apply IHM1 with nN1 (stype_nl_pi_intro tau2 tau).
  assumption.
  exists nM'.
  assumption.
  intros.
  intro.
  inversion H0.
  inversion H1.
  inversion H.
  apply IHM1 with nN1 (stype_nl_pi_intro tau2 tau).
  assumption.
  exists nM'.
  assumption.
  intros.
  intro.
  inversion H0.
  inversion H1.
  inversion H.
  apply IHM1 with nN1 (stype_nl_pi_intro tau2 tau).
  assumption.
  exists nM'.
  assumption.
  intros.
  inversion H.
  inversion H4.  
  intros.
  intro.
  destruct H0.
  inversion H0.
  inversion H.
  apply IHM1 with nN1 (stype_nl_pi_intro tau2 tau).
  assumption.
  exists nM'.
  assumption.
Qed.  
  
Lemma eq_nTy':
  forall (m n : nat) (sS : snsgn) (sG : snctx) (A1 A2 : nTy) (kappa : snK),
    n <= m -> n = depth_nTy A1 ->
    wfssig_nl sS ->
    ( walgeq_nl_Ty sS sG A1 A2 kappa )
      \/ ~ (walgeq_nl_Ty sS sG A1 A2 kappa).
Proof.
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
  apply cstu_nTy_inj with A1_2.
  assumption.
  assumption.
  rewrite H18 in H17.
  assert (nB2' = x0).
  apply cstu_nTy_inj with A2_2.
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

Lemma eq_nTy:
  forall (sS : snsgn) (sG : snctx) (A1 A2 : nTy) (kappa : snK),
    wfssig_nl sS ->
    ( walgeq_nl_Ty sS sG A1 A2 kappa ) \/ ~ (walgeq_nl_Ty sS sG A1 A2 kappa).
Proof.
  intros.
  eauto using eq_nTy'.
Qed.
    
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
  apply cstu_nK_inj with L1; assumption.
  rewrite H18.
  assert (x0 = nL').
  apply cstu_nK_inj with L2; assumption.
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
  