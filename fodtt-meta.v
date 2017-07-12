Load fodtt.

(*** metatheorems ***)

(** strenghtening **)

Lemma wfsig_nl_strenghtening_l :
  forall (S : nsgn) (c : con) (C : nTy),
    wfsig_nl ( (inl (c , C)) :: S) -> wfsig_nl S.
Proof.
  intros; inversion H; assumption.
Qed.

Lemma wfsig_nl_strenghtening_r :
  forall (S : nsgn) (alpha : tcon) (K : nK),
    wfsig_nl ( (inr (alpha , K)) :: S) -> wfsig_nl S.
Proof.
  intros; inversion H; assumption.
Qed.

Lemma wfctx_nl_strenghtening :
  forall (S : nsgn) (G : nctx) (C : nTy) ,
    wfctx_nl S (C :: G) -> wfctx_nl S G /\ wftype_nl S G C kind_nl_type.
Proof.
  intros; inversion H.
  split; assumption; assumption.  
Qed.

Lemma boundnTCon_strenghtening_l :
  forall (S : nsgn) (alpha : tcon) (L : nK) (c : con) (C : nTy),
    boundnTCon alpha L (inl (c, C) :: S) ->
    boundnTCon alpha L S.
Proof.
  intros.
  unfold boundnTCon in H; decompose record H.
  destruct x.
  replace ( nsigempty ++ inr (alpha, L) :: x0) with ( inr (alpha, L) :: x0) in H0
    by (cbv; auto).
  inversion H0.
  apply ex_intro with  x.
  apply ex_intro with x0.
  split.
  replace ((s :: x) ++ inr (alpha, L) :: x0)
  with (s :: (x ++ inr (alpha, L) :: x0)) in H0.
  inversion H0.
  reflexivity.
  apply app_comm_cons.
  intro.
  destruct H2.
  cbv.
  right; assumption.
Qed.

Lemma boundnTCon_strenghtening_r :
  forall (S : nsgn) (alpha beta : tcon) (L M : nK),
    boundnTCon alpha L (inr (beta, M) :: S) ->
    alpha <> beta ->
    boundnTCon alpha L S.
Proof.
  intros.
  unfold boundnTCon in H; decompose record H.
  destruct x.
  replace ( nsigempty ++ inr (alpha, L) :: x0) with ( inr (alpha, L) :: x0) in H1
    by (cbv; auto).
  inversion H1.
  symmetry in H4; contradiction.
  apply ex_intro with  x.
  apply ex_intro with x0.
  split.
  replace ((s :: x) ++ inr (alpha, L) :: x0)
  with (s :: (x ++ inr (alpha, L) :: x0)) in H1
  by (apply app_comm_cons).
  inversion H1.
  reflexivity.
  intro.
  destruct H3.
  cbv.
  right; assumption.
Qed.


Lemma boundnCon_strenghtening_l :
  forall (S : nsgn) (beta : tcon) (c d: con) (C D : nTy),
    boundnCon c C (inl (d, D) :: S) ->
    c <> d ->
    boundnCon c C S.
Proof.
  intros.
  unfold boundnCon in H; unfold boundnCon; decompose record H.
  destruct x.
  replace ( nsigempty ++ inl (c, C) :: x0) with ( inl (c, C) :: x0) in H1
    by (cbv; auto). 
  inversion H1.
  symmetry in H4; contradiction.
  apply ex_intro with x.
  apply ex_intro with x0.
  split.
  replace ((s :: x) ++ inl (c, C) :: x0)
  with (s :: (x ++ inl (c, C) :: x0)) in H1
  by (apply app_comm_cons).
  inversion H1.
  reflexivity.
  intro.
  destruct H3.
  cbv.
  right; assumption.
Qed.

Lemma boundnCon_strenghtening_r :
  forall (S : nsgn) (alpha : tcon) (L : nK) (c : con) (C : nTy),
    boundnCon c C (inr (alpha, L) :: S) ->
    boundnCon c C S.
Proof.
  intros.
  unfold boundnCon in H; decompose record H.
  destruct x.
  replace ( nsigempty ++ inl (c, C) :: x0) with ( inl (c, C) :: x0) in H0
    by (cbv; auto).
  inversion H0.
  apply ex_intro with  x.
  apply ex_intro with x0.
  split.
  replace ((s :: x) ++ inl (c, C) :: x0)
  with (s :: (x ++ inl (c, C) :: x0)) in H0
  by (apply app_comm_cons).
  inversion H0.
  reflexivity.
  intro.
  destruct H2.
  cbv.
  right; assumption.
Qed.

(** weakening **)

Lemma boundnTCon_weakening_l:
  forall (S : nsgn) (alpha : tcon) (L : nK) (c: con) (C: nTy),
    boundnTCon alpha L S ->
    boundnTCon alpha L (inl(c , C) :: S). 
Proof.
  intros; unfold boundnTCon; unfold boundnTCon in H; decompose record H.
  apply ex_intro with (inl(c, C) :: x). 
  apply ex_intro with x0. 
  split.
  rewrite H0. 
  apply app_comm_cons.
  apply not_in_cons.
  split.
  replace (fstnSig (inl(c,C))) with (@inl con tcon c) by (cbv; auto).
  discriminate.
  assumption.
Qed.

Lemma boundnTCon_weakening_r:
  forall (S : nsgn) (alpha beta : tcon) (L M : nK),
    wfsig_nl (inr(beta, M) :: S) ->
    boundnTCon alpha L S ->
    boundnTCon alpha L (inr(beta , M) :: S).
Proof.
  intros; unfold boundnTCon; unfold boundnTCon in H0; decompose record H0.
  rewrite H1.
  apply ex_intro with (inr(beta, M) :: x).
  apply ex_intro with x0.
  split.
  trivial.
  apply not_in_cons.
  split.  
  replace (fstnSig (inr(beta,M))) with (@inr con tcon beta) by (cbv; auto).
  simplify_eq.
  intro.
  inversion H.
  destruct H10.
  rewrite H1.
  rewrite <- H4.
  apply ex_intro with L.
  apply ex_intro with x.
  apply ex_intro with x0.
  split.
  trivial.
  assumption.
  assumption.
Qed.  

Lemma boundnCon_weakening_l :
  forall (S : nsgn) (c d : con) (C D : nTy),
    wfsig_nl (inl (d, D) :: S) ->
    boundnCon c C S ->
    boundnCon c C (inl (d, D) :: S).
Proof.
  intros; unfold boundnCon; unfold boundnCon in H0; decompose record H0.
  rewrite H1.
  apply ex_intro with (inl(d, D) :: x).
  apply ex_intro with x0.
  split.
  trivial.
  apply not_in_cons.
  split.  
  replace (fstnSig (inl(d,D))) with (@inl con tcon d) by (cbv; auto).
  simplify_eq.
  intro.
  inversion H.
  destruct H10.
  rewrite H1.
  rewrite <- H4.
  apply ex_intro with C.
  apply ex_intro with x.
  apply ex_intro with x0.
  split.
  trivial.
  assumption.
  assumption.
Qed.

Lemma boundnCon_weakening_r :
  forall (S : nsgn) (alpha : tcon) (L : nK) (c : con) (C : nTy),
    boundnCon c C S ->
    boundnCon c C (inr (alpha, L) :: S).
Proof.
  intros; unfold boundnCon; unfold boundnCon in H; decompose record H.
  rewrite H0.
  apply ex_intro with (inr(alpha, L) :: x).
  apply ex_intro with x0.
  split.
  trivial.
  apply not_in_cons.
  split.  
  replace (fstnSig (inr(alpha,L))) with (@inr con tcon alpha) by (cbv; auto).
  simplify_eq.
  assumption.
Qed.  

(* TODO: why do we need the lemma? *)

Lemma indomnTCon_wf_neq:
  forall (S : nsgn) (alpha beta : tcon) (L : nK),
    wfsig_nl (inr (beta, L) :: S) -> 
    ~ indomnTCon alpha (inr (beta, L) :: S) ->
    alpha <> beta.
Proof.
  intros.
  intro.
  destruct H0.
  rewrite H1.
  inversion H.
  apply ex_intro with L.
  apply ex_intro with nsigempty.
  apply ex_intro with S.
  split.
  trivial.
  intro.
  destruct H7.
Qed.

Lemma boundnTCon_wf_kieq_r:
  forall (S : nsgn) (alpha : tcon) (L M : nK),
    wfsig_nl (inr (alpha, L) :: S) -> 
    boundnTCon alpha M (inr (alpha, L) :: S) ->
    M = L.
Proof.
  intros.
  unfold boundnTCon in H0; decompose record H0; clear H0.
  destruct x.
  inversion H1.
  reflexivity.
  inversion H1.
  destruct H3.
  rewrite <- H2.
  replace (map fstnSig (inr (alpha, L) :: x)) with ((inr alpha) :: (map fstnSig x)) by (cbv; auto).
  cbv.
  left; reflexivity.
Qed.


Lemma boundnTCon_wf_kieq:
  forall (S : nsgn) (alpha : tcon) (L M : nK),
    boundnTCon alpha M S ->
    boundnTCon alpha L S ->
    M = L.
Proof.
  intros.
  induction S.
  (* base case *)
  inversion H.
  decompose record H1.
  apply app_cons_not_nil in H3.
  contradiction.
  destruct a.
  destruct p.
  apply boundnTCon_strenghtening_l in H.
  apply boundnTCon_strenghtening_l in H0.
  apply IHS.
  assumption.
  assumption.
  (* step case *)
  destruct p.
  unfold boundnTCon in H; decompose record H.
  unfold boundnTCon in H0; decompose record H0.
  destruct x.
  replace (nsigempty ++ inr (alpha, M) :: x0) with (inr(alpha, M) :: x0) in H1
  by (cbv; auto).
  inversion H1.
  destruct x1.
  replace (nsigempty ++ inr (alpha, L) :: x2) with (inr(alpha, L) :: x2) in H2
  by (cbv; auto).
  inversion H2.
  rewrite <- H7; rewrite <- H10; trivial.
  rewrite H1 in H2.
  replace ((s :: x1) ++ inr (alpha, L) :: x2) with (s :: (x1 ++ inr(alpha,L) :: x2)) in H2
    by (cbv; auto).  
  inversion H2.
  rewrite <- H9 in H5.
  destruct H5.
  cbv; left; reflexivity.
  destruct x1.
  replace (nsigempty ++ inr (alpha, L) :: x2) with (inr(alpha, L) :: x2) in H2
  by (cbv; auto).
  inversion H2.
  rewrite H1 in H2.
  replace ((s :: x) ++ inr (alpha, M) :: x0) with (s :: (x ++ inr(alpha,M) :: x0)) in H2
    by (cbv; auto).  
  inversion H2.
  rewrite H9 in H3.
  destruct H3.
  cbv; left; reflexivity.
  apply IHS.
  apply ex_intro with x.
  apply ex_intro with x0.
  split.
  replace ((s :: x) ++ inr (alpha, M) :: x0) with (s :: (x ++ inr(alpha,M) :: x0)) in H1
    by (cbv; auto).    
  inversion H1.
  trivial.
  intro.
  destruct H3.
  cbv; right; assumption.
  apply ex_intro with x1.
  apply ex_intro with x2.
  split. 
  replace ((s0 :: x1) ++ inr (alpha, L) :: x2) with (s0 :: (x1 ++ inr(alpha,L) :: x2)) in H2
    by (cbv; auto).    
  inversion H2.
  trivial.
  intro.
  destruct H5.
  cbv; right; assumption.
Qed.
  
  (*
Lemma boundnTCon_wf_neq:
  forall (S : nsgn) (alpha beta : tcon) (L M : nK),
    wfsig_nl (inr (beta, L) :: S) -> 
    ~ boundnTCon alpha M (inr (beta, L) :: S) ->
    alpha <> beta.
Proof.
  intros.
  intro.
  destruct H0.
  rewrite H1.
  inversion H.
(*  apply ex_intro with L.*)
  apply ex_intro with nsigempty.
  apply ex_intro with S.
  split.
  trivial.
  intro.
  destruct H7.
Qed.  
*)

Lemma indomnTCon_weakening_decompose:
  forall (S : nsgn) (alpha : tcon) (a : con * nTy + tcon * nK),
    (wfsig_nl (a :: S)) ->
    (~ indomnTCon alpha (a :: S)) ->
    (inr(alpha) <> fstnSig(a)) /\ (~ indomnTCon alpha S).
Proof.
  intros.
  destruct a.
  destruct p.
  split.
  replace (fstnSig (inl (c, n))) with (@inl con tcon c) by (cbv; auto).
  simplify_eq.
  intro.
  inversion H1.
  apply H0.
  inversion H.
  unfold boundnTCon in H2.
  decompose record H2.
  apply ex_intro with x.
  apply ex_intro with (inl(c,n) :: x0).
  apply ex_intro with x1.
  split.
  rewrite H9.
  trivial.
  intro.
  replace (map fstnSig (inl (c, n) :: x0))
  with (@inl con tcon c :: (map fstnSig x0)) in H10 by (cbv; auto).
  inversion H10.
  inversion H12.
  contradiction.
  (* right branch *)
  destruct p.
  split.  
  replace (fstnSig (inr (t, n))) with (@inr con tcon t) by (cbv; auto).
  simplify_eq.
  apply indomnTCon_wf_neq with (alpha := alpha) in H.
  assumption.
  assumption.
  intro.
  apply indomnTCon_wf_neq with (alpha := alpha) in H.
  destruct H0.
  unfold indomnTCon in H1; unfold boundnTCon in H1; decompose record H1.
  apply ex_intro with x.
  apply ex_intro with (inr (t, n) :: x0).
  apply ex_intro with x1.
  split.
  rewrite H2; trivial.
  intro.
  destruct H3.
  inversion H0.
  inversion H3.
  symmetry in H5; contradiction.
  assumption.
  assumption.
Qed.

(** wellformedness of substructures **)

Lemma wfctx_nl_wfsub:
  forall ( S : nsgn ) ( G : nctx ),
    wfctx_nl S G ->
    wfsig_nl S.
Proof.
  intros.
  induction G. 
  inversion H.
  assumption.
  apply wfctx_nl_strenghtening in H.
  destruct H.
  exact (IHG H).
Qed.

Lemma wftype_nl_wfsub:
  forall ( S : nsgn ) ( G : nctx ) ( C : nTy) (K : nK),
    wftype_nl S G C K ->
    wfsig_nl S /\ wfctx_nl S G .
Proof.
  intros.
  generalize dependent K0.
  generalize G.
  induction C.
  (* base case *)
  intros.
  inversion H.
  split.
  apply wfctx_nl_wfsub in H1.
  assumption.
  assumption.
  (* induction - pi_elim *)
  intros.
  inversion H.
  apply IHC in H4.
  assumption.
  (* induction - pi_intro *)
  intros.
  inversion H.
  apply IHC2 in H5; decompose [ and ] H5.
  split.
  assumption.
  inversion H7.
  assumption.
Qed.

(*
Lemma wfterm_nl_wfsub:
  forall ( S : nsgn ) ( G : nctx ) ( C : nTy) (P : nte),
    wfterm_nl S G P C ->
    wfsig_nl S /\ wfctx_nl S G.  
Proof.
*)
(*  
Lemma wfsig_tcon :
  forall (S : nsgn) (G : nctx) (alpha : tcon) (L : nK),
    wfsig_nl S -> boundnTCon alpha L S -> wfkind_nl S G L.
Proof.
*)

(*
Lemma wfctx_nl_weakening_sgn_l:
  forall (S : nsgn) (G : nctx) (c : con) (C : nTy),
    wfctx_nl S G ->
    wfsig_nl ( (inl (c, C)) :: S) ->
    wfctx_nl ( (inl (c, C)) :: S) G
with wftype_nl_weakening_sgn_l:
  forall (S : nsgn) (G : nctx) (c : con) (L : nK) (C D : nTy),
    wftype_nl S G C L ->
    wfsig_nl (inl (c, D) :: S) ->
    wftype_nl (inl (c, D) :: S) G C L
with wfterm_nl_weakening_sgn_l:
  forall (S : nsgn) (G : nctx) (c : con) (K : nK) (C D : nTy) (P : nte),
    wfterm_nl S G P C ->
    wfsig_nl (inl (c, D) :: S) ->
    wfterm_nl (inl (c, D) :: S) G P C
.
Proof.
  admit.
  admit.
  admit.
Admitted.

Lemma wfterm_nl_weakening_ctx:
  forall (S : nsgn) (G : nctx) (C D : nTy) (P : nte),
    wfterm_nl S G P C ->
    wftype_nl S G D kind_nl_type ->
    wfterm_nl S (D :: G) (pdecte P) (pdecTy C).
Proof.
(*  intros.
  generalize dependent C.
  induction G.
  induction P.
  replace (pdecte (term_nl_cdb cdb5))
  with (term_nl_cdb (cdb_succ cdb5))
    by (cbv; auto).
  intros.
  apply te_nl_var.
  apply ctx_nl_var.
  apply wftype_nl_wfsub in H0.
  decompose record H0.
  assumption.
  assumption.
  inversion H.
  induction cdb5.
  inversion H1.
  
  destruct C.
  replace  (pdecTy (type_nl_tcon tcon5))
  with (type_nl_tcon tcon5)
    by (cbv; auto).
  assumption.
  inversion H.
  
  replace (pdecTy (type_nl_pi_elim C nte5))
  with (type_nl_pi_elim (pdecTy C) (pdecte nte5))
    by (cbv;cbv;auto).
  inversion H
 *)
  admit.
Admitted.
 *)

Lemma wftype_nl_weaken_lemma:
  forall (C D : nTy),
    wftype_nl nsigempty (C :: nctxempty) D kind_nl_type ->
    wftype_nl nsigempty nctxempty D kind_nl_type.
Admitted.
  
Lemma wftype_nsigempty_nctxempty:
  forall (C : nTy) (G : nctx) (L : nK),
    ~ wftype_nl nsigempty G C L.
Proof.
  intros.
  generalize dependent L.
  (*  induction G. *)
  generalize dependent G.
  induction C.
  (* case type_nl_tcon alpha *)
  intros.
  intro.
  inversion H.
  unfold boundnTCon in H4.
  decompose record H4.
  apply app_cons_not_nil in H6.
  contradiction.
  (* case type_nl_pi_intro *)
  intros.
  intro.
  inversion H.
  destruct IHC with (G) (kind_nl_pi_intro D nK5).
  assumption.
  (* case type_nl_pi_intro *)
  intros.
  intro.
  inversion H.
  destruct IHC2 with (C1 :: G) (kind_nl_type).
  assumption.
Qed.

Lemma wftype_cdb_zero_nonempty':
  forall (C : nTy),
    ~wfterm_nl nsigempty nctxempty (term_nl_cdb cdb_zero) C.
Proof.
  intros.
  intro.
  inversion H.
  clear H6.
  clear H5. clear C'.
  clear H4. clear H3.
  clear H2.
  inversion H1.
  
  destruct C.
  inversion H.  
  inversion H1.
  inversion H11.
  decompose record H13.
  apply app_cons_not_nil in H15.
  contradiction.
  inversion H.
  inversion H1.  
  inversion H12.
  unfold boundnTCon in H15.
  decompose record H15.
  apply app_cons_not_nil in H20.
  contradiction.
  inversion H15.
  unfold boundnTCon in H15.
  decompose record H15.
  apply app_cons_not_nil in H20.
  contradiction.
   *)
  
Lemma wfctx_nl_weakening_sgn_r:
  forall (S : nsgn) (G : nctx) (alpha : tcon) (K : nK),
    wfsig_nl ( (inr (alpha, K)) :: S) ->
    wfctx_nl S G ->
    wfctx_nl ( (inr (alpha, K)) :: S) G
with wftype_nl_weakening_sgn_r:
  forall (S : nsgn) (G : nctx) (alpha : tcon) (K L : nK) (C : nTy),
    wfsig_nl (inr (alpha, K) :: S) ->
    wftype_nl S G C L ->
    wftype_nl (inr (alpha, K) :: S) G C L
with wfterm_nl_weakening_sgn_r:
  forall (S : nsgn) (G : nctx) (alpha : tcon) (K : nK) (C : nTy) (P : nte),
    wfsig_nl (inr (alpha, K) :: S) ->
    wfterm_nl S G P C ->
    wfterm_nl (inr (alpha, K) :: S) G P C.
Proof.
  (* lem 1 *)
  intros.
  induction G.
  apply ctx_nl_empty.
  assumption.
  apply wfctx_nl_strenghtening in H0.
  destruct H0.
  apply ctx_nl_var.
  apply IHG.
  assumption.
  apply wftype_nl_weakening_sgn_r.
  assumption.
  assumption.
  (* lem 2 *)
  intros.
  induction C.
  inversion H0.
  apply ty_nl_tcon.
  apply wfctx_nl_weakening_sgn_r.  
  assumption.
  assumption.  
  apply boundnTCon_weakening_r.
  assumption.
  assumption.
(*  inversion H.
  assumption.*)
  (* case ty_nl_pi_elim *)
  inversion H0.  
  apply ty_nl_pi_elim with D. 
  apply wftype_nl_weakening_sgn_r.
  assumption.
  assumption.
  apply wfterm_nl_weakening_sgn_r.
  assumption.
  assumption.
  (* case ty_nl_pi_intro *)
  inversion H0.
  apply ty_nl_pi_intro.
  apply wftype_nl_weakening_sgn_r.
  assumption.
  assumption.
  (* lem 3 *)
  intros.
  generalize dependent G.
  generalize dependent C.
  induction P.
  (* case te_nl_cdb *)
  induction cdb5.
  inversion H.  
  intros.
  destruct G.

  (* TODO apply no cdb in nctzempty *)
  inversion H6.
  
  apply te_nl_var_z.
  
  generalize dependent C.
  inversion H.
  induction cdb5.
  induction G.
  intros.
  apply te_nl_var_z.
  apply wfctx_nl_weakening_sgn_r.
  assumption.
  assumption.
  intros.
  apply IHG.
  
  apply wfterm_nl_wfsub in H0.
  decompose [and] H.
  assumption.
  apply wfterm_nl_weakening_sgn_r.
  apply te_nl_conv with (C := C0).
  assumption.
  assumption.
  assumption.  
  assumption.
  
  inversion H.
  inversion H1.
  apply wftype_nl_weakening_sgn_r.
  assumption.
  assumption.
  apply wftype_nl_weakening_sgn_r.
  assumption.
  assumption.
  inversion H.
  apply wfterm_nl_weakening_ctx with (D := C0) in H.
  
  apply IHcdb5 in H5.
  apply te_nl_var.

    
  destruct C.
  eapply te_nl_var. 
  apply wfctx_nl_weakening_sgn_r.
  apply ctx_nl_var.
  apply wfterm_nl_wfsub in H.
  decompose record H.
  assumption.
  inversion H.
  inversion H2.
  assumption.
  apply IHcdb5 in H.
  
  admit. (* project wftype_nl from wfterm *)
  assumption.
  apply wfterm_nl_weakening_sgn_r.
  assumption.
  assumption.
  apply wfterm_nl_weakening_sgn_r.
  assumption.
  assumption.
  apply wfterm_nl_weakening_sgn_r.
  assumption.
  assumption.
  apply wfterm_nl_weakening_sgn_r.
  assumption.
  assumption.
  apply wfterm_nl_weakening_sgn_r.
  assumption.
  assumption.
Admitted.
  
 *)
(*
Lemma wfkind_nl_weakening_sgn_r :
  forall (S : nsgn) (G : nctx) (alpha : tcon) (K L : nK),
    wfkind_nl S G L ->
    wfsig_nl ( (inr (alpha, K)) :: S) ->
    wfkind_nl ( (inr (alpha, K)) :: S) G L
.
Proof.
  intros.
  generalize dependent G.
  induction L.
  intros.
  apply k_nl_type.  
  apply wfctx_nl_weakening_sgn_r.
  inversion H.
  assumption.
  assumption.
  intros.
  apply k_nl_pi_intro.
  inversion H.
  apply IHL in H4.
  assumption.
Qed.
 *)
(*
Lemma wfkind_nl_weakening_ctx_r :
  forall (S : nsgn) (G : nctx) (C : nTy) (L : nK),
    wfkind_nl S G L ->
    wfctx_nl S (C :: G) ->
    wfkind_nl S (C :: G) (pdecK L).
Proof.
  intros.
  generalize dependent G.
  induction L.
  (* case kind_nl_type *)
  intros.
  apply k_nl_type.
  assumption.
  (* case kind_nl_pi_intro *)
  intros.
  inversion H.
*)

(*
Lemma wfsig_con :
  forall (S : nsgn) (c : con) (C : nTy),
    wfsig_nl S -> boundnCon c C S -> exists K , wftype_nl S nctxempty C K.

Lemma wfctx_type :
  forall (S : nsgn) (G : nctx) (C : nTy) ,
    wfctx_nl S (C :: G) -> wftype_nl S G C kind_nl_type.
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Lemma wfsig_type :
  forall (S : nsgn) (G : nctx) (c : con) (C : nTy),
    wfsig_nl S ->
    boundnCon c C S ->
    wftype_nl S G C kind_nl_type.
Proof.
  intros.
  generalize G.
  induction S.
  destruct H0.
  destruct H0.
  decompose [and] H0.
  apply (app_cons_not_nil) in H1.
  contradiction.
  intro.
  destruct a.
  inversion H.
  admit.
  inversion H.
  apply IHS with G0 in H3.
  apply wftype_nl_weakening_sgn_r.
  assumption.
  rewrite H1.
  assumption.
  rewrite <- H1 in H0.
  apply boundnCon_strenghtening_r in H0.
  assumption.
Admitted.
 *)

(*
Lemma boundnCon_type :
  forall (S : nsgn) (G : nctx) (c : con) (C : nTy) ,
    wfsig_nl S ->
    boundnCon c C S ->
    (wftype_nl S G C kind_nl_type).
Proof.
  intros.
  induction S.
  destruct H0.
  destruct H0.
  decompose [and] H0.
  inversion H.
  apply app_cons_not_nil in H1.
  contradiction.
  destruct a.
  admit.
  inversion H.
  rewrite <- H1 in H0.
  apply boundnCon_strenghtening_r in H0.
  apply IHS in H3.
  apply wftype_nl_weakening_sgn_r.
  assumption.
  rewrite <- H1 in H.
  assumption.
  assumption.
Admitted.
 *)
(*
Lemma wfterm_type :
  forall (S : nsgn) (G : nctx) (P : nte) (C : nTy) ,
    wfterm_nl S G P C -> exists K , (wftype_nl S G C K).
Proof.
  intros.
  induction P.
  induction cdb5. 
  apply ex_intro with kind_nl_type.
  inversion H.
  inversion H0.
  assumption.
  assumption.
  inversion H.
  apply IHcdb5 in H4.
  assumption.
  apply ex_intro with kind_nl_type.
  assumption.
  (* case pdb *)
  induction pdb5.
  inversion H.
  apply ex_intro with kind_nl_type.
  assumption.
  inversion H.
  apply ex_intro with kind_nl_type.
  assumption.
  (* case con *)
  inversion H.
  apply wfctx_nl_wfsub in H1.
  apply boundnCon_type with (G := G) (c := con5) (C := C) in H1.
  apply ex_intro with kind_nl_type.
  assumption.
  assumption.
  apply ex_intro with kind_nl_type.
  assumption.
  (* case term_pi_intro *)
  admit.
  (* case term_pi_elim *)
  admit.
Admitted.
*)
Theorem id_incdecte :
  forall (S : nsgn) (G : nctx) (P : nte) (C : nTy) ,
    wfterm_nl S G P C -> pincte (pdecte P) = P
with id_incdecty :
  forall (S : nsgn) (G : nctx) (C : nTy) (K : nK),
    wftype_nl S G C K -> pincTy (pdecTy C) = C.
Proof.
  (* in_incdecte *)
  intros.
  induction P.
  replace (pdecte (term_nl_cdb cdb5)) with (term_nl_cdb (cdb_succ cdb5)) by (cbv; reflexivity).
  replace (pincte (term_nl_cdb (cdb_succ cdb5))) with (term_nl_cdb cdb5) by (cbv; reflexivity).
  reflexivity.
  case pdb5.
  replace (pdecte (term_nl_pdb (pdb_zero))) with (term_nl_cdb cdb_zero)
    by (cbv;reflexivity).
  replace (pincte (term_nl_cdb cdb_zero)) with (term_nl_pdb pdb_zero)
    by (cbv; reflexivity).
  reflexivity.
  intro.
  replace (pdecte (term_nl_pdb (pdb_succ pdb0))) with (term_nl_pdb pdb0)
    by (cbv;reflexivity).
  replace (pincte (term_nl_pdb pdb0)) with (term_nl_pdb (pdb_succ pdb0))
    by (cbv; reflexivity).
  reflexivity.
  replace (pdecte (term_nl_con con5)) with (term_nl_con con5) by (cbv; reflexivity).
  replace (pincte (term_nl_con con5)) with (term_nl_con con5) by (cbv; reflexivity).
  reflexivity.
  replace (pdecte (term_nl_pi_intro nTy5 P))
  with (term_nl_pi_intro (pdecTy nTy5) (pdecte P))
    by (cbv; reflexivity).
  replace (pincte (term_nl_pi_intro (pdecTy nTy5) (pdecte P)))
  with (term_nl_pi_intro (pincTy (pdecTy nTy5)) (pincte (pdecte P)))
    by (cbv; reflexivity).
  f_equal.
  admit.
  admit.
  admit.

  (* case Ty *)
  admit.
Admitted.


           
           