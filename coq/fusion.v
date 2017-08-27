Require Import defns.

(** decidability and determinacy of cs **)

Lemma cs_nTy_dec:
  forall (A : nTy),
    { A' : nTy | cs_nTy A A' } 
with cs_nte_dec:
  forall (M : nte),
    {  M' : nte | cs_nte M M' }.
Proof.
  intros.
  induction A.
  exists (typestar_nl_tcon tcon5).
  apply cs_nTy_tcon.
  destruct IHA1.
  destruct IHA2.
  exists (typestar_nl_pi_intro x x0).
  apply cs_nTy_pi_intro.
  assumption. assumption.
  destruct IHA.
  assert ({M' | cs_nte nte5 M'}) by (apply cs_nte_dec).
  destruct H.
  exists (typestar_nl_pi_elim x x0).
  auto using cs_nTy_pi_elim.
  (* cs_nte_dec *)
  intros.
  induction M.
  exists (termstar_nl_con con5).
  constructor.
  exists (termstar_nl_ixc (S ixc)).
  constructor.
  exists (termstar_nl_ixt ixt).
  constructor.
  destruct IHM.
  assert ({A' | cs_nTy nTy5 A'}) by (apply cs_nTy_dec).
  destruct H.
  exists (termstar_nl_pi_intro x0 x).
  auto using cs_nte_pi_intro.
  destruct IHM1.
  destruct IHM2.
  exists (termstar_nl_pi_elim x x0).
  apply cs_nte_pi_elim.
  assumption.
  assumption.
Qed.

Lemma cs_nTy_determinacy:
  forall (A B1 B2 : nTy),
    cs_nTy A B1 -> cs_nTy A B2 ->
    B1 = B2           
with cs_nte_determinacy:
  forall (M N1 N2 : nte),
    cs_nte M N1 -> cs_nte M N2 ->
    N1 = N2.
Proof.
  intros.
  generalize dependent B2.
  generalize dependent B1.
  induction A.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply IHA1.
  auto.
  auto.
  apply IHA2.
  auto.
  auto.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply IHA.
  auto.
  auto.
  apply cs_nte_determinacy with nte5.
  auto.
  auto.
  (* cs_nte_determinacy lemma *)
  intros.
  generalize dependent N2.
  generalize dependent N1.
  induction M.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply cs_nTy_determinacy with nTy5. 
  auto.
  auto.
  apply IHM.
  auto.
  auto.
  intros.
  inversion H.
  inversion H0.
  f_equal.
  apply IHM1.
  auto.
  auto.
  apply IHM2.
  auto.
  auto.
Qed.
  
(** decidability and determinacy of cstu **)

Lemma cstu_nTy_dec:
  forall (A : nTy),
    { A' : nTy | cstu_nTy A A' } + {forall A',  ~ (cstu_nTy A A')}
with cstu_nte_dec:
  forall (M : nte),
    {  M' : nte | cstu_nte M M' } + {forall M',  ~ (cstu_nte M M')}.
Proof.
  intros.
  induction A.
  left.
  exists (typestar_nl_tcon tcon5); trivial using cstu_nTy_tcon.
  destruct IHA1; destruct IHA2.
  left.
  destruct s;  destruct s0.
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
  assert ({M' : nte |  cstu_nte nte5 M'} +
      {forall M' : nte, ~ cstu_nte nte5 M'}) by (apply cstu_nte_dec).
  destruct H.
  left.
  destruct s.
  destruct s0.
  exists (typestar_nl_pi_elim x x0); apply cstu_nTy_pi_elim; assumption.
  (* the other sub case *)
  right.
  intro.
  intro.
  inversion s; inversion H; apply n with nM'; assumption.
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
  assert ({A' : nTy | cstu_nTy nTy5 A'} +
          {forall A' : nTy, ~ cstu_nTy nTy5 A'}).
  apply cstu_nTy_dec.
  destruct H.
  left.
  destruct s.
  destruct s0.
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
  destruct s.
  destruct s0.
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
    { L' | cstu_nK L L'} + {forall L',  ~ (cstu_nK L L')}.
Proof.
  intros.
  induction L.
  left.
  exists kindstar_nl_type.
  apply cstu_K_type.
  (* step case *)
  assert ({A' : nTy | cstu_nTy nTy5 A'} + 
          {forall A' : nTy, ~ cstu_nTy nTy5 A'}).
  apply cstu_nTy_dec.
  destruct IHL.
  destruct H.
  left.
  destruct s.
  destruct s0.
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

Lemma cstu_nTy_determinacy:
  forall (A B1 B2 : nTy),
    cstu_nTy A B1 -> cstu_nTy A B2 ->
    B1 = B2           
with cstu_nte_determinacy:
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
  apply cstu_nte_determinacy with nte5.
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
  apply cstu_nTy_determinacy with nTy5.
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

Lemma cstu_nK_determinacy:
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
  apply cstu_nTy_determinacy with nTy5.
  assumption.
  assumption.
  apply IHL.
  assumption.
  assumption.
Qed.

(** decidability and determinacy of cuts **)

Lemma cuts_nTy_dec:
  forall (A : nTy),
    { A' | cuts_nTy A A' } + {forall A',  ~ (cuts_nTy A A')}
with cuts_nte_dec:
  forall (M : nte),
    { M' | cuts_nte M M' } + {forall M',  ~ (cuts_nte M M')}.
Proof.
  intros.
  induction A.
  left.
  exists (typestar_nl_tcon tcon5).
  trivial using cuts_nTy_tcon.
  destruct IHA1.
  destruct IHA2.
  left.
  destruct s.
  destruct s0.
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
  assert ({M' |  cuts_nte nte5 M'} +
      {forall M' : nte, ~ cuts_nte nte5 M'}) by (apply cuts_nte_dec).
  destruct H.
  left.
  destruct s.
  destruct s0.
  exists (typestar_nl_pi_elim x x0).
  apply cuts_nTy_pi_elim.
  assumption.
  assumption.
  (* the other sub case *)
  right.
  intro.
  intro.
  inversion H.
  inversion s.
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
  assert ({A' | cuts_nTy nTy5 A'} +
          {forall A' : nTy, ~ cuts_nTy nTy5 A'}).
  apply cuts_nTy_dec.
  destruct H.
  left.
  destruct s.
  destruct s0.
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
  destruct s.
  destruct s0.
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
  
Lemma cuts_nTy_determinacy:
  forall (A B1 B2 : nTy),
    cuts_nTy A B1 -> cuts_nTy A B2 ->
    B1 = B2           
with cuts_nte_determinacy:
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
  apply cuts_nte_determinacy with nte5; assumption; assumption.
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
  apply cuts_nTy_determinacy with nTy5; assumption; assumption.
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
    { A' | tuts_nTy A N A' } + {forall A',  ~ (tuts_nTy A N A')}
with tuts_nte_dec:
  forall (M N : nte),
    { M' | tuts_nte M N M' } + {forall M',  ~ (tuts_nte M N M')}.
Proof.
  intros.
  induction A.
  left.
  exists (typestar_nl_tcon tcon5).
  trivial using tuts_nTy_tcon.
  destruct IHA1.
  destruct IHA2.
  left.
  destruct s.
  destruct s0.
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
  assert ({M' | tuts_nte nte5 N M'} + 
      {forall M' : nte, ~ tuts_nte nte5 N M'}) by (apply tuts_nte_dec).
  destruct H.
  left.
  destruct s.
  destruct s0.
  exists (typestar_nl_pi_elim x x0).
  auto using tuts_nTy_pi_elim.
  (* the other sub case *)
  right.
  intro.
  intro.
  inversion s.
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
  assert ({A' | tuts_nTy nTy5 N A'} +
          {forall A' : nTy, ~ tuts_nTy nTy5 N A'}).
  apply tuts_nTy_dec.
  destruct H.
  left.
  destruct s.
  destruct s0.
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
  destruct s.
  destruct s0.
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

Lemma tuts_nTy_determinacy:
  forall (A B1 B2: nTy) (N : nte),
    tuts_nTy A N B1 -> tuts_nTy A N B2 ->
    B1 = B2
with tuts_nte_determinacy:
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
  apply tuts_nte_determinacy with nte5 N; assumption; assumption.
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
  apply tuts_nTy_determinacy with nTy5 N; assumption; assumption.
  apply IHM; assumption; assumption.
  (* pi_elim *)
  intros.
  inversion H; inversion H0; f_equal.
  apply IHM1; assumption; assumption.
  apply IHM2; assumption; assumption.
Qed.

