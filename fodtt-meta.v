Load fodtt.

(*** metatheorems ***)

(** structural properties of pincte, pdecte, pincTy and pdecTy **)


Lemma id_incdecte :
  forall (P : nte),
    pincte (pdecte P) = P
with id_incdecTy :
  forall (C : nTy),
    pincTy (pdecTy C) = C.
Proof.
  intros.
  induction P.
  cbv; reflexivity.
  destruct pdb5.
  cbv; reflexivity.
  cbv; reflexivity.
  cbv; reflexivity.
  replace (pincte (pdecte (term_nl_pi_intro nTy5 P)))
  with (term_nl_pi_intro (pincTy (pdecTy nTy5)) (pincte (pdecte P)))
  by (cbv; reflexivity).
  f_equal.
  apply id_incdecTy.
  apply IHP.
  replace (pincte (pdecte (term_nl_pi_elim P1 P2)))
  with (term_nl_pi_elim (pincte (pdecte P1)) (pincte (pdecte P2)))
  by (cbv; reflexivity).
  f_equal.
  apply IHP1.
  apply IHP2.
  (* lemma incdecTy *)
  intros.
  induction C.
  cbv; reflexivity.
  replace (pincTy (pdecTy (type_nl_pi_elim C nte5)))
  with (type_nl_pi_elim (pincTy (pdecTy C)) (pincte (pdecte nte5)))
  by (cbv; reflexivity).
  f_equal.
  apply IHC.
  apply id_incdecte.
  replace (pincTy (pdecTy (type_nl_pi_intro C1 C2)))
  with (type_nl_pi_intro (pincTy (pdecTy C1)) (pincTy (pdecTy C2)))
  by (cbv; reflexivity).
  f_equal.
  apply IHC1.
  apply IHC2.
Qed.

Lemma id_decincte :
  forall (P : nte),
    pdecte (pincte P) = P
with id_decincTy :
  forall (C : nTy),
    pdecTy (pincTy C) = C.
Proof.
  intros.
  induction P.
  destruct cdb5.
  cbv; reflexivity.
  cbv; reflexivity.
  cbv; reflexivity.
  cbv; reflexivity.
  replace (pdecte (pincte (term_nl_pi_intro nTy5 P)))
  with (term_nl_pi_intro (pdecTy (pincTy nTy5)) (pdecte (pincte P)))
  by (cbv; reflexivity).
  f_equal.
  apply id_decincTy.
  apply IHP.
  replace (pdecte (pincte (term_nl_pi_elim P1 P2)))
  with (term_nl_pi_elim (pdecte (pincte P1)) (pdecte (pincte P2)))
  by (cbv; reflexivity).
  f_equal.
  apply IHP1.
  apply IHP2.
  (* lemma decincTy *)
  intros.
  induction C.
  cbv; reflexivity.
  replace (pdecTy (pincTy (type_nl_pi_elim C nte5)))
  with (type_nl_pi_elim (pdecTy (pincTy C)) (pdecte (pincte nte5)))
  by (cbv; reflexivity).
  f_equal.
  apply IHC.
  apply id_decincte.
  replace (pdecTy (pincTy (type_nl_pi_intro C1 C2)))
  with (type_nl_pi_intro (pdecTy (pincTy C1)) (pdecTy (pincTy C2)))
  by (cbv; reflexivity).
  f_equal.
  apply IHC1.
  apply IHC2.
Qed.

(** strenghtening **)

Lemma wfsig_nl_strenghtening :
  forall (S : nsgn) (a : con*nTy + tcon*nK),
    wfsig_nl ( a :: S) ->
    wfsig_nl S.
Proof.
  intros; inversion H; assumption.
Qed.

Lemma wfsig_nl_strenghtening_r :
  forall (S : nsgn) (alpha : tcon) (K : nK),
    wfsig_nl ( (inr (alpha , K)) :: S)
    -> wfsig_nl S.
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
  apply IHG.
  apply wfctx_nl_strenghtening in H.
  decompose record H.
  assumption.
Qed.

Lemma wftype_nl_wfsub:
  forall ( S : nsgn ) ( G : nctx ) ( C : nTy) (K : nK),
    wftype_nl S G C K ->
    wfsig_nl S /\ wfctx_nl S G .
Proof.
  intros.
  induction H.
  (* base case *)
  intros.
  split.
  apply wfctx_nl_wfsub with nctx5.
  assumption.
  assumption.
  (* induction - pi_elim *)
  intros.
  decompose record IHwftype_nl.
  split.
  assumption.
  inversion H1.
  assumption.
  assumption.
Qed.

Lemma wfterm_nl_wfsub:
  forall ( S : nsgn ) ( G : nctx ) ( C : nTy) (P : nte),
    wfterm_nl S G P C ->
    wfsig_nl S /\ wfctx_nl S G .
Proof.
  intros.
  induction H.
  (* base *)
  intros.
  split.
  apply wfctx_nl_wfsub in H.
  assumption.
  assumption.
  split.
  apply wfctx_nl_wfsub in H.
  assumption.
  assumption.
  split.
  decompose record IHwfterm_nl.
  assumption.
  assumption.
  decompose record IHwfterm_nl.
  split.
  assumption.
  apply wfctx_nl_strenghtening in H1.
  decompose record H1.
  assumption.
  assumption.
  assumption.
Qed.  

(** weakening **)

Lemma boundnCon_weakening :
  forall (S : nsgn) (a : con*nTy + tcon*nK) (c : con) (C : nTy),
    wfsig_nl (a :: S) ->
    boundnCon c C S ->
    boundnCon c C (a :: S).
Proof.
  intros; unfold boundnCon; unfold boundnCon in H0; decompose record H0.
  rewrite H1.
  apply ex_intro with (a :: x).
  apply ex_intro with x0.
  split.
  trivial.
  apply not_in_cons.
  split.
  destruct a.
  destruct p.
  replace (fstnSig (inl(c0,n))) with (@inl con tcon c0) by (cbv; auto).
  simplify_eq.
  intro.
  inversion H.
  destruct H10.
  apply ex_intro with C.
  apply ex_intro with x.
  apply ex_intro with x0.
  split.
  trivial.
  rewrite <- H4.
  assumption.
  rewrite <- H4.
  assumption.
  destruct p.
  replace (fstnSig (inr(t,n))) with (@inr con tcon t) by (cbv; auto).
  simplify_eq.
  assumption.
Qed.

Lemma boundnTCon_weakening:
  forall (S : nsgn) (a : con*nTy + tcon * nK) (alpha : tcon) (L : nK),
    wfsig_nl (a :: S) ->
    boundnTCon alpha L S ->
    boundnTCon alpha L (a :: S).
Proof.
  intros; unfold boundnTCon; unfold boundnTCon in H0; decompose record H0.
  rewrite H1.
  apply ex_intro with (a :: x).
  apply ex_intro with x0.
  split.
  trivial.
  apply not_in_cons.
  split.
  destruct a.
  destruct p.
  replace (fstnSig (inl(c,n))) with (@inl con tcon c) by (cbv; auto).
  discriminate.
  destruct p.
  replace (fstnSig (inr(t,n))) with (@inr con tcon t) by (cbv; auto).
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

Lemma wfctx_nl_weakening_sgn:
  forall (S : nsgn) (G : nctx) (a : con*nTy + tcon * nK),
    wfsig_nl ( a :: S) ->
    wfctx_nl S G ->
    wfctx_nl ( a :: S) G
with wftype_nl_weakening_sgn:
  forall (S : nsgn) (G : nctx) (a : con*nTy + tcon * nK) (L : nK) (C: nTy),
    wfsig_nl (a :: S) ->
    wftype_nl S G C L ->
    wftype_nl (a :: S) G C L
with wfterm_nl_weakening_sgn:
  forall (S : nsgn) (G : nctx) (a : con*nTy + tcon * nK) (C : nTy) (P : nte),
    wfsig_nl (a :: S) ->
    wfterm_nl S G P C ->
    wfterm_nl (a :: S) G P C
with substaptype_nl_weakening_sgn:
  forall (S : nsgn) (G : nctx) (a : con*nTy + tcon * nK) (L : nK) (D1 D2 : nTy),
    wfsig_nl (a :: S) ->
    substaptype_nl S G D1 D2 L ->
    substaptype_nl (a :: S) G D1 D2 L
with substapterm_nl_weakening_sgn:
  forall (S : nsgn) (G : nctx) (a : con*nTy + tcon * nK) (C D : nTy) (P Q : nte),
    wfsig_nl (a :: S) ->
    substapterm_nl S G P Q D ->
    substapterm_nl (a :: S) G P Q D.
Proof.
  (* lemma wfctx_nl_weakening_sgn *)
  intros.
  induction H0.
  (* base case *)
  apply ctx_nl_empty.
  assumption.
  (* step case *)
  apply ctx_nl_var.
  apply IHwfctx_nl.
  assumption.
  apply wftype_nl_weakening_sgn.
  assumption.
  assumption.
  (* lemma wftype_nl_weakening_sgn *)
  intros.
  induction H0.
  (* base case tcon *)
  apply ty_nl_tcon.
  apply wfctx_nl_weakening_sgn.
  assumption.
  assumption.
  apply boundnTCon_weakening.
  assumption.
  assumption.
  (* step case pi intro *)
  apply ty_nl_pi_intro.
  apply IHwftype_nl.
  assumption.
  (* step case pi elim *)
  apply ty_nl_pi_elim with D.
  apply IHwftype_nl.
  assumption.
  apply wfterm_nl_weakening_sgn.
  assumption.
  assumption.
  (* lemma wfterm_nl_weakening *)
  intros.
  induction H0.
  apply te_nl_con.
  apply wfctx_nl_weakening_sgn.
  assumption.
  assumption.
  apply boundnCon_weakening.
  assumption.
  assumption.
  (* step case cdb_zero *)
  apply te_nl_var_z.
  apply wfctx_nl_weakening_sgn.
  assumption.
  assumption.
  (* step case sdb_succc *)
  apply te_nl_var.
  apply wfctx_nl_weakening_sgn.
  assumption.
  assumption. 
  apply IHwfterm_nl.
  assumption.
  (* step case pi intro *)
  apply te_nl_pi_intro.
  apply IHwfterm_nl.
  assumption.
  (* step case pi elim *)
  apply te_nl_pi_elim with C.
  apply IHwfterm_nl1.
  assumption.
  apply IHwfterm_nl2.
  assumption.
  (* step case conv *)
  apply te_nl_conv with C.
  apply IHwfterm_nl.
  assumption.
  apply wftype_nl_weakening_sgn.
  assumption.
  assumption.
  apply substaptype_nl_weakening_sgn.
  assumption.
  assumption.
  (* lemma substaptype_nl_weakening_sgn *)
  intros.
  induction H0.
  apply eqT_nl_refl.
  apply wftype_nl_weakening_sgn.
  assumption.
  assumption.
  (* step case sym *)
  apply eqT_nl_sym.
  apply IHsubstaptype_nl.
  assumption.
  (* step case trans *)
  apply eqT_nl_trans with C_2.
  apply IHsubstaptype_nl1.
  assumption.
  apply IHsubstaptype_nl2.
  assumption.
  (* step case pi intro *)
  apply eqT_nl_1.
  apply IHsubstaptype_nl1.
  assumption.
  apply IHsubstaptype_nl2.
  assumption.
  (* step case pi elim *)
  apply eqT_nl_2.
  apply IHsubstaptype_nl.
  assumption.
  apply substapterm_nl_weakening_sgn.
  assumption.
  assumption.
  assumption.
  (* lemma substapterm_nl_weakening_sgn *)
  intros.
  induction H0.
  apply eqt_nl_refl.
  apply wfterm_nl_weakening_sgn.
  assumption.
  assumption.
  (* case sym *)
  apply eqt_nl_sym.
  apply IHsubstapterm_nl.
  assumption.
  (* case trans *)
  apply eqt_nl_trans with (Q_2 := Q_2).
  apply IHsubstapterm_nl1.
  assumption.
  apply IHsubstapterm_nl2.
  assumption.
  (* case pi_elim *)
  apply eqt_nl_1 with (D := D).
  apply IHsubstapterm_nl1.
  assumption.
  apply IHsubstapterm_nl2.
  assumption.
  (* case pi_elim *)
  apply eqt_nl_2 with (D := D).
  apply IHsubstapterm_nl1.
  assumption.
  apply IHsubstapterm_nl2.
  assumption.
  (* case app *)
  apply eqt_nl_3.
  apply substaptype_nl_weakening_sgn.
  assumption.
  assumption.
  apply IHsubstapterm_nl.
  assumption.
Qed.

Lemma wfkind_nl_weakening_sgn :
  forall (S : nsgn) (G : nctx) (a : con*nTy + tcon * nK) (L : nK),
    wfsig_nl ( a :: S) ->
    wfkind_nl S G L ->
    wfkind_nl ( a :: S) G L.
Proof.
  intros.
  induction H0.
  apply k_nl_type.  
  apply wfctx_nl_weakening_sgn.
  assumption.
  assumption.
  apply k_nl_pi_intro.
  apply IHwfkind_nl.
  assumption.
Qed.


Lemma wftype_nl_strenghtening_ctx:
  forall (S : nsgn) (G : nctx) (C D : nTy),
    wftype_nl S (D :: G) (pincTy C) kind_nl_type ->
    wftype_nl S G C kind_nl_type.
Proof.
  intros.
  induction C.
  replace (pincTy (type_nl_tcon tcon5))
  with (type_nl_tcon tcon5)
    in H by (cbv; auto).
  inversion H.
  apply ty_nl_tcon.
  inversion H1.
  assumption.
  assumption.
  (* case pi elim *)
  admit.
  (* case pi intro *)
(*  apply ty_nl_pi_intro.
  
  remember (D :: G) as G' in H.
  remember (pincTy C) as C' in H.
  induction H.
  destruct C.
  apply ty_nl_tcon.
  rewrite HeqG' in H.
  inversion H.
  assumption.
  admit.
  admit.
  admit.
  (* step case *)
  apply IHwftype_nl.

  *)
  (*
Lemma wftype_nl_exchange_ctx:
  forall (S : nsgn) (G : nctx) (L : nK) (C D1 D2 : nTy),
    wfctx_nl S (D2 :: G) ->
    wftype_nl S (pincTy D2 :: D1 :: G) (pincTy C) L ->
    wftype_nl S (pincTy D1 :: D2 :: G) (pincTy C) L
with (*
    wfctx_nl S (D2 :: G) ->
    (*wfctx_nl S (D1 :: G) ->  *)
    wftype_nl S (D2 :: D1 :: G) C L ->
    wftype_nl S (D1 :: D2 :: G) C L
(*with wfterm_nl_exchange_ctx:
  forall (S : nsgn) (G : nctx) (P : nte) (C D1 D2 : nTy),
    wfctx_nl S (D1 :: G) ->
    wfterm_nl S (D1 :: D2 :: G) P C ->
    wfterm_nl S (D2 :: D1 :: G) P C
       *)
with*) (*wfctx_nl_weakening_ctx: (* exchange ?? *)
  forall (S : nsgn) (G : nctx) (C D : nTy),
    wfctx_nl S (C :: G) ->
    wfctx_nl S (D :: G) ->
    wfctx_nl S (D :: C :: G)
with *) wftype_nl_weakening_ctx:
  forall (S : nsgn) (G : nctx) (L : nK) (C D : nTy),
    wfctx_nl S (D :: G) ->
    wftype_nl S G C L ->
    wftype_nl S (D :: G) (pincTy C) L              
with wfterm_nl_weakening_ctx:
  forall (S : nsgn) (G : nctx) (C D : nTy) (P : nte),
    wfctx_nl S (D :: G) ->
    wfterm_nl S G P C ->
    wfterm_nl S (D :: G) P C
with substaptype_nl_weakening_ctx:
  forall (S : nsgn) (G : nctx) (L : nK) (D C1 C2 : nTy),
    wfctx_nl S (D :: G) ->
    substaptype_nl S G C1 C2 L ->
    substaptype_nl S (D :: G) C1 C2 L
with substapterm_nl_weakening_ctx:
  forall (S : nsgn) (G : nctx) (C D : nTy) (P Q : nte),
    wfctx_nl S (D :: G) ->
    substapterm_nl S G P Q C ->
    substapterm_nl S (D :: G) P Q C.
Proof.
  (* lemma wftype_nl_exchange_ctx *)
  intros.
  remember (pincTy D2 :: D1 :: G) as G' in H0.
  remember (pincTy C) as C' in H0.
  induction H0.
  (* base case tcon *)
  rewrite <- HeqC'.
  rewrite HeqG' in H0.
  apply ty_nl_tcon.
  apply ctx_nl_var.
  assumption.
  inversion H0.
  inversion H5.
  apply wftype_nl_weakening_ctx.
  assumption.
  assumption.
  assumption.
  (* step case pi intro *)
  apply wftype_nl_weakening_ctx.
  apply ctx_nl_var.
  assumption.
  apply wftype_nl_weakening_ctx.
  assumption.
  rewrite HeqG' in H0.
  apply wftype_nl_wfsub in H0; decompose record H0.
  inversion H2; inversion H6; inversion H11.
  assumption.
 
  apply wftype_nl_strenghtening_ctx.


  
(*  rewrite Heqctx in H1. *)
  (*generalize D1 D2 G H H0. *)
  induction H0.
  (* base case tcon *)
  intros.
  apply ty_nl_tcon.
  apply wfctx_nl_weakening_ctx.
  assumption.
  rewrite Heqctx in H0.
  inversion H0.
  assumption.
  assumption.
  (* step case pi intro *)
  intros.
  rewrite Heqctx in H1.
  apply ty_nl_pi_intro.
  apply wftype_nl_weakening_ctx.
  apply wftype_nl_wfsub in H1; decompose record H1.
  assumption.
  apply IHwftype_nl.
  
  apply wftype_nl_weakening_ctx.
  apply ctx_nl_var.
  apply wftype_nl_wfsub in H0; decompose record H0.
  assumption.
  inversion H.
  apply wftype_nl_weakening_ctx.
  apply wftype_nl_wfsub in H0; decompose record H0.
  assumption.
  assumption.
  assumption.
  (* lemma wfterm_nl_exchange_ctx *)
  (* admit. *)
 *)
  (* lemma wfctx_nl_weakening_ctx *)
(*  intros.
  induction G.
  (* base case *)
  apply ctx_nl_var.
  assumption.
  inversion H0.
  apply wftype_nl_weakening_ctx.
  assumption.
  assumption.
  (* step case *)
  apply ctx_nl_var.
  assumption.
  inversion H0.
  apply wftype_nl_weakening_ctx.
  assumption.
  assumption.
  (* lemma  wftype_nl_weakening_ctx *)
  intros.
  generalize H.
  generalize D.
  clear H.
  induction H0.
  (* base case *)
  intros.
  replace (pincTy (type_nl_tcon alpha))
  with (type_nl_tcon alpha)
  by (cbv; auto).
  apply ty_nl_tcon.
  assumption.
  assumption.
  (* step case pi intro *)
  intros.
  replace (pincTy (type_nl_pi_intro C (pincTy D0)))
  with (type_nl_pi_intro (pincTy C) (pincTy (pincTy D0)))
  by (cbv; auto).
  apply ty_nl_pi_intro.
  apply IHwftype_nl.
  apply ctx_nl_var.
  assumption.
  inversion H1.
  apply wftype_nl_wfsub in H5; decompose record H5.


  admit.
  apply IHwftype_nl.
  apply ctx_nl_var.
  apply wftype_nl_wfsub in H0; decompose record H0.
  assumption.
  apply wftype_nl_weakening_ctx. (* !!!! *)
  apply wftype_nl_wfsub in H0; decompose record H0.
  assumption.
  inversion H.
  assumption.
  apply IHwftype_nl.
  admit. (* from generalised IH? *)
  (* case pi elim *)
  apply ty_nl_pi_elim with (D := D0).
  apply IHwftype_nl.
  assumption.
  apply wfterm_nl_weakening_ctx.
  apply ctx_nl_var.
  apply wftype_nl_wfsub in H; decompose record H.
  assumption.
  assumption.
  assumption.
  (* wfterm_nl_weakening_ctx *)
  intros.
  induction H0.
  (* base case con *)
  apply te_nl_con.
  assumption.
  assumption.
  (* base case cdb_zero *)
  apply wfterm_nl_exchange_ctx.
  assumption.
  apply te_nl_var_z.
  admit. (* ??? *)
  (* step case sdb_succ *)
  apply wfterm_nl_exchange_ctx.
  assumption.
  apply te_nl_var.
  admit. (* ??? *)
  apply IHwfterm_nl.
  admit. (* ??? *)
  (* step case pi intro *)
  apply te_nl_pi_intro.
  apply wfterm_nl_exchange_ctx.
  assumption.
  apply IHwfterm_nl.
  admit. (* ??? *)
  (* step case pi elim *)
  apply te_nl_pi_elim with C.
  apply IHwfterm_nl1.
  assumption.
  apply IHwfterm_nl2.
  assumption.
  apply te_nl_conv with C.
  apply IHwfterm_nl.
  assumption.
  apply wftype_nl_weakening_ctx.
  inversion H.
  assumption.
  assumption.
  apply substaptype_nl_weakening_ctx.
  assumption.
  assumption.
  (* lemma substaptype_nl_weakening_ctx *)
  intros.
  induction H0.
  (* base case refl *)
  apply eqT_nl_refl.
  apply wftype_nl_weakening_ctx.
  inversion H.
  assumption.
  assumption.
  (* base case sym *)
  apply eqT_nl_sym.
  apply IHsubstaptype_nl.
  assumption.
  (* step case trans *)
  apply eqT_nl_trans with C_2.
  apply IHsubstaptype_nl1.
  assumption.
  apply IHsubstaptype_nl2.
  assumption.
  (* step case pi intro *)
  apply eqT_nl_1.
  apply IHsubstaptype_nl1.
  assumption.
  apply IHsubstaptype_nl2.
  assumption.
  (* step case pi elim *)
  apply eqT_nl_2.
  apply IHsubstaptype_nl.
  assumption.
  apply substapterm_nl_weakening_ctx.
  assumption.
  assumption.
  (* lemma substapterm_nl_weakening_ctx *)
  intros.
  induction H0.
  (* base case refl *)
  apply eqt_nl_refl.
  apply wfterm_nl_weakening_ctx.
  assumption.
  assumption.
  (* step case sym *)
  apply eqt_nl_sym.
  apply IHsubstapterm_nl.
  assumption.
  (* step case trans *)
  apply eqt_nl_trans with Q_2.
  apply IHsubstapterm_nl1.
  assumption.
  apply IHsubstapterm_nl2.
  assumption.
  (* step case pi intro *)
  apply eqt_nl_1 with D0.
  apply IHsubstapterm_nl1.
  assumption.
  apply IHsubstapterm_nl2.
  assumption.
  (* step case pi elim *)
  apply eqt_nl_2 with D0.
  apply IHsubstapterm_nl1.
  assumption.
  apply IHsubstapterm_nl2.
  assumption.
  (* step case app *)
  apply eqt_nl_3.
  apply substaptype_nl_weakening_ctx.
  assumption.
  assumption.
  apply IHsubstapterm_nl.
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


Lemma wfctx_nl_bound_kind:
  forall ( S : nsgn ) ( C : nTy) (c : con),
    wfsig_nl S ->
    boundnCon c C S ->
    wftype_nl S nctxempty C kind_nl_type.
Proof.
  intros.
  induction S.
  (* base case *)
  unfold boundnCon in H0; decompose record H0.
  apply app_cons_not_nil in H1.
  contradiction.
  (* step case *)
  destruct a.
  destruct p.
  unfold boundnCon in H0; decompose record H0.
  induction x.
  replace (nsigempty ++ inl(c,C) :: x0) with (inl(c,C) :: x0) in H1 by (cbv;auto).
  inversion H1.
  inversion H.
  rewrite <- H5.

(*
Lemma wfterm_nl_wftype_nl:
  forall ( S : nsgn ) ( G : nctx ) ( C : nTy) (P : nte),
    wfterm_nl S G P C ->
    exists L , wftype_nl S G C L.
Proof.
  intros.
  induction H.
  induction nsgn5.
  (* base case *)
  admit.

  
  intros.
  inversion H.
  apply boundnCon_nsigempty in H1.
  contradiction.
  inversion H0.
  apply wftype_nl_nsigempty in H9.
  contradiction.
  inversion H0.
  apply wftype_nl_nsigempty in H10.
  contradiction.
  apply ex_intro with (kind_nl_type).
  apply ty_nl_pi_intro.
*)



           
           