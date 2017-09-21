Require Import defns.

(** * Context shifting **)

(** decidability of context shifting **)

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

Lemma cs_nK_dec:
  forall (L : nK),
    { L' : nK | cs_nK L L' }.
Proof.
  intros.
  induction L.
  eexists.
  econstructor.
  destruct IHL.
  assert ({nTy5' : nTy | cs_nTy nTy5 nTy5'}) by (apply cs_nTy_dec).
  destruct H.
  eexists.
  econstructor; eauto.
Qed.

Lemma cs_nctx_dec:
  forall (G : nctx),
    { G' : nctx | cs_nctx G G' }.
Proof.
  intros.
  induction G.
  exists nil.
  constructor.
  assert ({A' : nTy | cs_nTy a A'}) by (apply cs_nTy_dec).
  destruct IHG.
  destruct H.
  eexists.
  eapply cs_nctx_var; eauto.
Qed.

(** determinacy of context shifting **)

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
  induction H.
  intros.
  inversion H0; auto.
  intros; inversion H1.
  f_equal.
  apply IHcs_nTy1; auto.
  apply IHcs_nTy2; auto.
  intros.
  inversion H1.
  f_equal.
  apply IHcs_nTy; auto.
  eapply cs_nte_determinacy; eauto.
  (* cs_nte_determinacy lemma *)
  intros.
  generalize dependent N2.
  induction H.
  intros.
  inversion H0; auto.
  intros; inversion H0; auto.
  intros; inversion H0; auto.
  intros; inversion H1.
  f_equal.
  eapply cs_nTy_determinacy; eauto. 
  apply IHcs_nte; auto.
  intros.
  inversion H1.
  f_equal.
  apply IHcs_nte1; auto.
  apply IHcs_nte2; auto.
Qed.

Lemma cs_nctx_determinacy:
  forall (G G1 G2 : nctx),
    cs_nctx G G1 -> cs_nctx G G2 ->
    G1 = G2.
Proof.
  induction G.
  intros.
  inversion H; inversion H0; constructor.
  intros.
  inversion H; inversion H0; f_equal.
  eapply cs_nTy_determinacy; eauto.
  eapply IHG; eauto.
Qed.

(** surjectivity of context shifting **)

Lemma cs_nTy_surjectivity:
  forall (A1 A2 B : nTy),
    cs_nTy A1 B -> cs_nTy A2 B ->
    A1 = A2           
with cs_nte_surjectivity:
  forall (M1 M2 N : nte),
    cs_nte M1 N -> cs_nte M2 N ->
    M1 = M2.
Proof.
  intros.
  generalize dependent A2.
  induction H.
  intros.
  inversion H0; auto.
  intros.
  inversion H1.
  f_equal.
  apply IHcs_nTy1; auto.
  apply IHcs_nTy2; auto.
  intros.
  inversion H1.
  f_equal.
  apply IHcs_nTy; auto.
  eapply cs_nte_surjectivity; eauto.
  (* cs_nte_determinacy lemma *)
  intros.
  generalize dependent M2.
  induction H.
  intros.
  inversion H0; auto.
  intros.
  inversion H0; auto.
  intros.
  inversion H0; auto.
  intros.
  inversion H1.
  f_equal.
  eapply cs_nTy_surjectivity; eauto. 
  apply IHcs_nte; auto.
  intros.
  inversion H1.
  f_equal.
  apply IHcs_nte1; auto.
  apply IHcs_nte2; auto.
Qed.

(** cstu preservers cs **)

Fixpoint cs_nTy_cstu (B C B' C' : nTy) (i : Ixc) (H : cs_nTy B C) {struct H}:
      cstu_nTy B i B' -> cstu_nTy C (S i) C' ->
      cs_nTy B' C'
with cs_nte_cstu (M N M' N' : nte) (i : Ixc) (H : cs_nte M N) {struct H}:
      cstu_nte M i M' -> cstu_nte N (S i) N' ->
      cs_nte M' N'.
Proof.
  (* Lemma 1 *)
  intros.
  generalize dependent C'.
  generalize dependent B'.
  induction H.
  (* tcon *)
  intros.
  inversion H0; inversion H1.
  constructor.
  (* pi_intro *)
  intros.
  inversion H1; inversion H2.
  apply cs_nTy_pi_intro.
  apply IHcs_nTy1; auto.
  apply IHcs_nTy2; auto.
  (* pi_elim *)
  intros.
  inversion H1; inversion H2.
  apply cs_nTy_pi_elim.
  apply IHcs_nTy; auto.
  eapply cs_nte_cstu; eauto.
  (* Lemma 2 *)
  intros.
  generalize dependent N'.
  generalize dependent M'.
  induction H.
  (* con *)
  intros.
  inversion H0; inversion H1.
  apply cs_nte_con.
  (* ixc S *)
  intros.
  inversion H0; inversion H1.
  apply cs_nte_ixc.
  (* ixc *)
  intros.
  destruct ixt.
  inversion H0; inversion H1.
  apply cs_nte_ixc.
  inversion H0; inversion H1.
  apply cs_nte_ixt.
  (* pi_intro *)
  intros.
  inversion H1; inversion H2.
  apply cs_nte_pi_intro.
  eapply cs_nTy_cstu; eauto.
  apply IHcs_nte; auto.
  (* pi_elim *)
  intros.
  inversion H1; inversion H2.
  apply cs_nte_pi_elim.
  apply IHcs_nte1; eauto.
  apply IHcs_nte2; eauto.
Defined.

(**
   * Context-shifting type-unshifting
 **)

(** decidability of cstu **)

Lemma cstu_nTy_dec:
  forall (A : nTy) (i : Ixc),
    { A' : nTy | cstu_nTy A i A' }
with cstu_nte_dec:
  forall (M : nte) (i : Ixc),
    {  M' : nte | cstu_nte M i M' }.
Proof.
  intros.
  induction A.
  (* case con *)
  eexists; constructor.
  (* case pi intro *)
  destruct IHA1; destruct IHA2.
  eexists; constructor; eauto.
  (* pi_elim *)
  destruct IHA.
  assert ({M' : nte |  cstu_nte nte5 i M'}) by (apply cstu_nte_dec).
  destruct H.
  eexists; constructor; eauto.
  (* lemma cstu_nte_dec *)
  intros.
  induction M.
  (* case con *)
  eexists; constructor.
  (* case ixc *)
  eexists; constructor.
  (* case ixt *)
  destruct ixt.
  eexists; constructor.
  eexists; constructor.
  (* case pi_intro *)  
  destruct IHM.
  assert ({A' : nTy | cstu_nTy nTy5 i A'}) by (apply cstu_nTy_dec).
  destruct H.
  eexists; constructor; eauto.
  (* case pi elim *)
  destruct IHM1.
  destruct IHM2.
  eexists; constructor; eauto.
Defined.

Lemma cstu_nK_dec:
  forall (L : nK) (i : Ixc),
    { L' | cstu_nK L i L'}.
Proof.
  intros.
  induction L.
  (* base case *)
  exists kindstar_nl_type.
  apply cstu_K_type.
  (* step case *)
  assert ({A' : nTy | cstu_nTy nTy5 i A'}).
  apply cstu_nTy_dec.
  destruct IHL.
  destruct H.
  exists (kindstar_nl_pi_intro x0 x).
  auto using cstu_K_pi_intro.
Qed.

(** determinacy od cstu **)

Lemma cstu_nTy_determinacy:
  forall (A B1 B2 : nTy) (i : Ixc),
    cstu_nTy A i B1 -> cstu_nTy A i B2 ->
    B1 = B2           
with cstu_nte_determinacy:
  forall (M N1 N2 : nte) (i : Ixc),
    cstu_nte M i N1 -> cstu_nte M i N2 ->
    N1 = N2.
Proof.
  intros.
  generalize dependent B2.
  induction H.
  intros.
  inversion H0; auto.
  intros.
  inversion H1; f_equal.
  apply IHcstu_nTy1; auto.
  apply IHcstu_nTy2; auto.
  (* elim *)
  intros.
  inversion H1; f_equal.
  eapply IHcstu_nTy; eauto.
  eapply cstu_nte_determinacy; eauto.
  (* lemma 2 *)
  intros.
  generalize dependent N2.
  induction H.
  intros.
  inversion H0; auto.
  intros.
  inversion H0; auto.
  intros.
  inversion H0; auto.
  intros.
  inversion H0; auto.
  (* pi_intro *)
  intros.
  inversion H1; f_equal.
  eapply cstu_nTy_determinacy; eauto.
  apply IHcstu_nte; auto.
  (* pi_elim *)
  intros.
  inversion H1; f_equal.
  apply IHcstu_nte1; auto.
  apply IHcstu_nte2; auto.
Qed.

Lemma cstu_nK_determinacy:
  forall (L L1 L2 : nK) (i : Ixt),
    cstu_nK L i L1 -> cstu_nK L i L2 ->
    L1 = L2.
Proof.
  intros.
  generalize dependent L1.
  generalize dependent L2.
  induction L.
  intros.
  inversion H; inversion H0; trivial.
  intros.
  inversion H; inversion H0; f_equal.
  eapply cstu_nTy_determinacy; eauto.
  apply IHL; auto.
Qed.

(** context-shifting preserves cstu **)

Fixpoint cstu_nTy_cs (A A' B B' : nTy) (i : Ixc) (H : cstu_nTy A i A') {struct H}:
         cs_nTy A B -> cs_nTy A' B' -> cstu_nTy B (S i) B'
with cstu_nte_cs (M M' N N' : nte) (i : Ixc) (H : cstu_nte M i M') {struct H}:
     cs_nte M N -> cs_nte M' N' -> cstu_nte N (S i) N'.        
Proof.
  (* lemma 1 *)
  intros.
  generalize dependent B'.
  generalize dependent B.
  induction H.
  intros.
  inversion H0; inversion H1; constructor.
  intros.
  inversion H1; inversion H2; constructor; eauto.
  intros.
  inversion H1. inversion H2; econstructor.
  eauto.
  eapply cstu_nte_cs; eauto.
  (* lemma 2 *)
  intros.
  generalize dependent N'.
  generalize dependent N.
  induction H.
  intros.
  inversion H0; inversion H1; constructor.
  intros.
  inversion H0; inversion H1; econstructor.
  intros.
  inversion H0; inversion H1; econstructor. 
  intros.
  inversion H0; inversion H1; econstructor.
  intros.
  inversion H1; inversion H2; econstructor.
  eapply cstu_nTy_cs; eauto.
  eauto.
  intros.
  inversion H1; inversion H2; econstructor; eauto.
Defined.  


(**
   * Context-unshifitng type-shifting
**)

(** decidability of cuts **)

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

(** determinacy of cuts **)

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
  generalize dependent B2.
  induction H.
  intros.
  inversion H0; auto.
  intros; inversion H1; f_equal.
  apply IHcuts_nTy1; auto.
  apply IHcuts_nTy2; auto.
  (* elim *)
  intros.
  inversion H1; f_equal.
  apply IHcuts_nTy; auto.
  eapply cuts_nte_determinacy; eauto.
  (* lemma 2 *)
  intros.
  generalize dependent N2.
  induction H.
  intros; inversion H0; auto.
  intros; inversion H0; auto. 
  intros; inversion H0; auto.
  intros; inversion H0; auto. 
  (* pi_intro *)
  intros.
  inversion H1; f_equal.
  eapply cuts_nTy_determinacy; eauto.  
  apply IHcuts_nte; auto.
  (* pi_elim *)
  intros.
  inversion H1; f_equal.
  apply IHcuts_nte1; auto.
  apply IHcuts_nte2; auto.
Qed.

(** 
   * Type-unshifting type-substitution
**)

(** decidability of tuts *)

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

(** determinacy of tuts *)

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
  generalize dependent B2.
  induction H.
  intros; inversion H0; auto.
  intros; inversion H1; f_equal.
  apply IHtuts_nTy1; auto.
  apply IHtuts_nTy2; auto.
  (* elim *)
  intros; inversion H1; f_equal.
  apply IHtuts_nTy; auto.
  eapply tuts_nte_determinacy; eauto.
  (* lemma 2 *)
  intros.
  generalize dependent N2.
  induction H.
  intros; inversion H0; auto.
  intros; inversion H0; auto.
  intros; inversion H0; auto.
  intros; inversion H0; auto.
  (* pi_intro *)
  intros.
  inversion H1; f_equal.
  eapply tuts_nTy_determinacy; eauto.
  apply IHtuts_nte; auto.
  (* pi_elim *)
  intros.
  inversion H1; f_equal.
  apply IHtuts_nte1; auto.
  apply IHtuts_nte2; auto.
Qed.

(** context shifting preserves tuts **)

Fixpoint tuts_nTy_cs (A B A' B': nTy) (N N' : nte) (H : tuts_nTy A N B) {struct H}:
    cs_nTy A A' -> cs_nTy B B' -> cs_nte N N' -> tuts_nTy A' N' B'
with tuts_nte_cs (M M' N csM csM' csN : nte) (H : tuts_nte M N M') {struct H}:
    cs_nte M csM -> cs_nte M' csM' -> cs_nte N csN -> tuts_nte csM csN csM'.
Proof.
  (* lemma 1 *)
  intros.
  generalize dependent B'.
  generalize dependent N'.
  generalize dependent A'.
  induction H.
  (* tcon *)
  intros; inversion H0; inversion H1; constructor.
  (* pi_intro *)
  intros; inversion H1; inversion H3; constructor.
  eapply IHtuts_nTy1; eauto.
  eapply IHtuts_nTy2; eauto.
  (* pi_elim *)
  intros; inversion H1; inversion H3; constructor.
  eapply IHtuts_nTy; eauto.
  eapply tuts_nte_cs; eauto.
  (* lemma 2 *)
  intros.
  generalize dependent csN.
  generalize dependent csM'.
  generalize dependent csM.            
  induction H.
  (* con *)
  intros; inversion H0; inversion H1; constructor.
  (* ixc *)
  intros; inversion H0; inversion H1; constructor.
  (* ixt 0 *)
  intros.
  inversion H0.
  assert (csN = csM') by (eauto using cs_nte_determinacy).
  rewrite H; constructor.
  (* ixt S i *)
  intros; inversion H0; inversion H1; constructor.
  (* pi case *)
  intros; inversion H1; inversion H2; constructor.
  eapply tuts_nTy_cs; eauto.
  apply IHtuts_nte; assumption.
  (* pi elim case *)
  intros; inversion H1; inversion H2; constructor.
  apply IHtuts_nte1; assumption.
  apply IHtuts_nte2; assumption.
Defined.

(** context shifting preserves tuts in inverse **)

Fixpoint tuts_nTy_cs_inverse (nA nA' A A' : nTy) (nN N : nte) (H : tuts_nTy nA nN nA') {struct H}:
  cs_nTy A nA -> cs_nte N nN -> cs_nTy A' nA' -> tuts_nTy A N A'
with tuts_nte_cs_inverse (nM nM' nN M N M' : nte) (H : tuts_nte nM nN nM') {struct H}:
       cs_nte M nM -> cs_nte N nN -> cs_nte M' nM' ->    tuts_nte M N M'.
Proof.
  (* lemma 1 *)
  intros.
  generalize dependent N.
  generalize dependent A'.
  generalize dependent A.
  induction H.
  intros.
  inversion H0; inversion H2.
  constructor. 
  intros.
  inversion H1; inversion H2.
  constructor.
  eapply IHtuts_nTy1; eauto.
  eapply IHtuts_nTy2; eauto.
  (* pi_elim *)
  intros.
  inversion H1; inversion H2.
  constructor.
  eapply IHtuts_nTy; eauto.
  eapply tuts_nte_cs_inverse; eauto.
  (* lemma 2 *)
  intros.
  generalize dependent N.
  generalize dependent M.
  generalize dependent M'.
  induction H.
  intros.
  inversion H0; inversion H2.
  constructor.
  intros.
  inversion H0; inversion H2.
  rewrite <- H4 in H6.
  inversion H6.
  constructor.
  (* ixt *)
  intros.
  inversion H0.
  assert (N = M') by (eapply cs_nte_surjectivity; eauto).
  rewrite H3.
  constructor.
  intros.
  inversion H0; inversion H2.
  constructor.
  intros.
  inversion H1; inversion H2.
  constructor.
  eapply tuts_nTy_cs_inverse; eauto.
  eapply IHtuts_nte; eauto.
  (* pi elim *)
  intros.
  inversion H1; inversion H2.
  constructor.
  eapply IHtuts_nte1; eauto.
  eapply IHtuts_nte2; eauto.
Defined.
