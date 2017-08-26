Require Import defns.

(** decidability and injectivity of cstu **)

Lemma cstu_nTy_dec:
  forall (A : nTy),
    { exists A' , cstu_nTy A A' } + {forall A',  ~ (cstu_nTy A A')}
with cstu_nte_dec:
  forall (M : nte),
    { exists M' , cstu_nte M M' } + {forall M',  ~ (cstu_nte M M')}.
Proof.
  intros.
  induction A.
  left.
  exists (typestar_nl_tcon tcon5); trivial using cstu_nTy_tcon.
  destruct IHA1; destruct IHA2.
  left.
  destruct e;  destruct e0.
  exists (typestar_nl_pi_intro x x0); auto using cstu_nTy_pi_intro.
  (* next case *)
  right.
  intros.
  intro.
  inversion H; eapply n with nB'; assumption.
  (* next case *)
  right.
  intros.
  intro.
  inversion H; apply n with nA'; assumption.
  (* pi intro ~ pi intro *)
  right.
  intros.
  intro.
  inversion H; apply n with nA'; assumption.
  (* next case *)
  destruct IHA.
  assert ({exists M' : nte, cstu_nte nte5 M'} +
      {forall M' : nte, ~ cstu_nte nte5 M'}) by (apply cstu_nte_dec).
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (typestar_nl_pi_elim x x0); apply cstu_nTy_pi_elim; assumption.
  (* the other sub case *)
  right.
  intro.
  intro.
  inversion e; inversion H; apply n with nM'; assumption.
  (* really last case :-) *)
  right.
  intro.
  intro.
  inversion H; apply n with nA'; assumption.
  (* lemma cstu_nte_dec *)
  intros.
  induction M.
  (* case con *)
  left.
  exists (termstar_nl_con con5); auto using cstu_nte_con.
  (* case ixc *)
  left.
  exists (termstar_nl_ixc (S ixc)); auto using cstu_nte_ixc.
  (* case ixt *)
  left.
  destruct ixt.
  exists (termstar_nl_ixc 0).
  apply cstu_nte_zerot.
  exists (termstar_nl_ixt ixt).
  apply cstu_nte_suct.
  (* case pi_intro *)  
  destruct IHM.
  assert ({exists A' : nTy, cstu_nTy nTy5 A'} +
          {forall A' : nTy, ~ cstu_nTy nTy5 A'}).
  apply cstu_nTy_dec.
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (termstar_nl_pi_intro x0 x).
  auto using cstu_nte_pi_intro.
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
Defined.

Lemma cstu_nK_dec:
  forall (L : nK),
    { exists L' , cstu_nK L L'} + {forall L',  ~ (cstu_nK L L')}.
Proof.
  intros.
  induction L.
  left.
  exists kindstar_nl_type.
  apply cstu_K_type.
  (* step case *)
  assert ({exists A' : nTy, cstu_nTy nTy5 A'} + 
          {forall A' : nTy, ~ cstu_nTy nTy5 A'}).
  apply cstu_nTy_dec.
  destruct IHL.
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (kindstar_nl_pi_intro x0 x).
  auto using cstu_K_pi_intro.
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
  generalize dependent H.
  generalize dependent H0.
  generalize dependent B2.
  generalize dependent B1.
  induction A.
  intros.
  inversion H; inversion H0.
  auto.
  intros.
  inversion H; inversion H0.
  f_equal.
  apply IHA1.
  assumption.
  assumption.
  apply IHA2.
  assumption.
  assumption.
  (* elim *)
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
  generalize dependent H0.
  generalize dependent H.
  generalize dependent N2.
  generalize dependent N1.
  induction M.
  intros.
  inversion H; inversion H0.
  auto.
  intros.
  inversion H; inversion H0.
  auto.
  intros.
  inversion H; inversion H0.
  auto.
  rewrite <- H2 in H4.
  inversion H4.
  rewrite <- H2 in H4.
  inversion H4.
  rewrite <- H2 in H4.
  inversion H4.
  auto.
  (* pi_intro *)
  intros.
  inversion H; inversion H0.
  f_equal.
  apply cstu_nTy_inj with nTy5.
  assumption.
  assumption.
  apply IHM.
  assumption.
  assumption.
  (* pi_elim *)
  intros.
  inversion H; inversion H0.
  f_equal.
  apply IHM1; assumption; assumption.
  apply IHM2; assumption; assumption.
Qed.

Lemma cstu_nK_inj:
  forall (L L1 L2 : nK),
    cstu_nK L L1 -> cstu_nK L L2 ->
    L1 = L2.
Proof.
  intros.
  generalize dependent L1.
  generalize dependent L2.
  induction L.
  intros.
  inversion H.
  inversion H0.
  trivial.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply cstu_nTy_inj with nTy5.
  assumption.
  assumption.
  apply IHL.
  assumption.
  assumption.
Qed.

(** decidability and injectivity of cuts **)

Lemma cuts_nTy_dec:
  forall (A : nTy),
    { exists A' , cuts_nTy A A' } + {forall A',  ~ (cuts_nTy A A')}
with cuts_nte_dec:
  forall (M : nte),
    { exists M' , cuts_nte M M' } + {forall M',  ~ (cuts_nte M M')}.
Proof.
  intros.
  induction A.
  left.
  exists (typestar_nl_tcon tcon5).
  trivial using cuts_nTy_tcon.
  destruct IHA1.
  destruct IHA2.
  left.
  destruct e.
  destruct e0.
  exists (typestar_nl_pi_intro x x0).
  auto using cuts_nTy_pi_intro.
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
  assert ({exists M' : nte, cuts_nte nte5 M'} +
      {forall M' : nte, ~ cuts_nte nte5 M'}) by (apply cuts_nte_dec).
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (typestar_nl_pi_elim x x0).
  apply cuts_nTy_pi_elim.
  assumption.
  assumption.
  (* the other sub case *)
  right.
  intro.
  intro.
  inversion H.
  inversion e.
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
  auto using cuts_nte_con.
  (* case ixc *)
  left.
  destruct ixc.
  exists (termstar_nl_ixt (0)).
  apply cuts_nte_zeroc.
  exists (termstar_nl_ixc ixc).
  apply cuts_nte_succ.
  (* case ixt *)
  left.
  exists (termstar_nl_ixt (S ixt)).
  apply cuts_nte_ixt.
  (* case pi_intro *)  
  destruct IHM.
  assert ({exists A' : nTy, cuts_nTy nTy5 A'} +
          {forall A' : nTy, ~ cuts_nTy nTy5 A'}).
  apply cuts_nTy_dec.
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (termstar_nl_pi_intro x0 x).
  auto using cuts_nte_pi_intro.
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
  auto using cuts_nte_pi_elim.
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
  
Lemma cuts_nTy_inj:
  forall (A B1 B2 : nTy),
    cuts_nTy A B1 -> cuts_nTy A B2 ->
    B1 = B2           
with cuts_nte_inj:
  forall (M N1 N2 : nte),
    cuts_nte M N1 -> cuts_nte M N2 ->
    N1 = N2.
Proof.
  intros.
  generalize dependent H.
  generalize dependent H0.
  generalize dependent B2.
  generalize dependent B1.
  induction A.
  intros.
  inversion H; inversion H0; auto.
  intros; inversion H; inversion H0; f_equal.
  apply IHA1; assumption; assumption.
  apply IHA2; assumption; assumption.
  (* elim *)
  intros.
  inversion H; inversion H0; f_equal.
  apply IHA; assumption; assumption.
  apply cuts_nte_inj with nte5; assumption; assumption.
  (* lemma 2 *)
  intros.
  generalize dependent H0.
  generalize dependent H.
  generalize dependent N2.
  generalize dependent N1.
  induction M.
  intros; inversion H; inversion H0; auto.
  intros; inversion H; inversion H0; rewrite <- H2 in H4; inversion H4; auto.
  intros; inversion H; inversion H0; rewrite <- H2 in H4; inversion H4; auto.
  (* pi_intro *)
  intros.
  inversion H; inversion H0; f_equal.
  apply cuts_nTy_inj with nTy5; assumption; assumption.
  apply IHM; assumption; assumption.
  (* pi_elim *)
  intros.
  inversion H; inversion H0; f_equal.
  apply IHM1; assumption; assumption.
  apply IHM2; assumption; assumption.
Qed.

(** decidability and injectivity of tuts *)
Lemma tuts_nTy_dec:
  forall (A : nTy) (N : nte) ,
    { exists A' , tuts_nTy A N A' } + {forall A',  ~ (tuts_nTy A N A')}
with tuts_nte_dec:
  forall (M N : nte),
    { exists M' , tuts_nte M N M' } + {forall M',  ~ (tuts_nte M N M')}.
Proof.
  intros.
  induction A.
  left.
  exists (typestar_nl_tcon tcon5).
  trivial using tuts_nTy_tcon.
  destruct IHA1.
  destruct IHA2.
  left.
  destruct e.
  destruct e0.
  exists (typestar_nl_pi_intro x x0).
  auto using tuts_nTy_pi_intro.
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
  assert ({exists M' : nte, tuts_nte nte5 N M'} + 
      {forall M' : nte, ~ tuts_nte nte5 N M'}) by (apply tuts_nte_dec).
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (typestar_nl_pi_elim x x0).
  auto using tuts_nTy_pi_elim.
  (* the other sub case *)
  right.
  intro.
  intro.
  inversion e.
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
  (* lemma tuts_nte_dec *)
  intros.
  induction M.
  (* case con *)
  left.
  exists (termstar_nl_con con5).
  auto using tuts_nte_con.
  (* case ixc *)
  left.
  exists (termstar_nl_ixc (ixc)).
  apply tuts_nte_ixc.
  (* case ixt *)
  left.
  destruct ixt.
  exists N.
  apply tuts_nte_ixt_zero.
  exists (termstar_nl_ixt ixt).
  apply tuts_nte_ixt_succ.
  (* case pi_intro *)  
  destruct IHM.
  assert ({exists A' : nTy, tuts_nTy nTy5 N A'} +
          {forall A' : nTy, ~ tuts_nTy nTy5 N A'}).
  apply tuts_nTy_dec.
  destruct H.
  left.
  destruct e.
  destruct e0.
  exists (termstar_nl_pi_intro x0 x).
  auto using tuts_nte_pi_intro.
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
  auto using tuts_nte_pi_elim.
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

Lemma tuts_nTy_inj:
  forall (A B1 B2: nTy) (N : nte),
    tuts_nTy A N B1 -> tuts_nTy A N B2 ->
    B1 = B2
with tuts_nte_inj:
  forall (M N N1 N2 : nte),
    tuts_nte M N N1 -> tuts_nte M N N2 ->
    N1 = N2.
Proof.
  intros.
  generalize dependent H.
  generalize dependent H0.
  generalize dependent B2.
  generalize dependent B1.
  induction A.
  intros; inversion H; inversion H0; auto.
  intros; inversion H; inversion H0; f_equal.
  apply IHA1; assumption; assumption.
  apply IHA2; assumption; assumption.
  (* elim *)
  intros; inversion H; inversion H0; f_equal.
  apply IHA; assumption; assumption.
  apply tuts_nte_inj with nte5 N; assumption; assumption.
  (* lemma 2 *)
  intros.
  generalize dependent H0.
  generalize dependent H.
  generalize dependent N2.
  generalize dependent N1.
  induction M.
  intros; inversion H; inversion H0; auto.
  intros; inversion H; inversion H0; auto.
  intros; inversion H; inversion H0.
  rewrite <- H3; inversion H6; auto.
  rewrite <- H5 in H2; inversion H2.
  rewrite <- H5 in H2; inversion H2.
  rewrite <- H5 in H2; inversion H2; reflexivity.
  (* pi_intro *)
  intros.
  inversion H; inversion H0; f_equal.
  apply tuts_nTy_inj with nTy5 N; assumption; assumption.
  apply IHM; assumption; assumption.
  (* pi_elim *)
  intros.
  inversion H; inversion H0; f_equal.
  apply IHM1; assumption; assumption.
  apply IHM2; assumption; assumption.
Qed.
