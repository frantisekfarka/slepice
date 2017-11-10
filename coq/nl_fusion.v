Require Import defns.

Require Import Arith.
Require Import List.

(** * Context shifting **)

(** decidability of context shifting **)

Lemma cs_nTy_dec:
  forall (A : nTy) (i : Ixc),
    { A' : nTy | cs_nTy A i A' } 
with cs_nte_dec:
  forall (M : nte) (i : Ixc),
    {  M' : nte | cs_nte M i M' }.
Proof.
  - induction A; intros i.

    + eexists; constructor.
    + destruct IHA1 with i.
      destruct IHA2 with i.
      eexists; constructor; eauto.
    + destruct IHA with i.
      assert ({M' | cs_nte nte5 i M'})
        as [ ]
          by (apply cs_nte_dec).
      eexists; constructor; eauto.

    + admit. (* from assumption on existence ?? *)
      
  - (* cs_nte_dec *)
    induction M; intro i.

    + eexists; constructor.

    + (* case ixc *)
      assert ({i <= ixc} + {ixc < i})
        as [ ]
          by (apply le_lt_dec).
      * exists (termstar_nl_ixc (S ixc)).

          generalize dependent ixc.
          induction i.
          { intros; constructor. }
          {  intros.
             destruct ixc.
             - inversion l.
             - constructor.
               apply IHi.
               apply le_S_n; auto. }
      * exists (termstar_nl_ixc ixc).
          generalize dependent ixc.
          induction i.
          intros.
          { inversion l. }
          { intros.
            destruct ixc.
            - constructor.
            - constructor.
              apply IHi.
              apply lt_S_n; auto. }
    + eexists; constructor.
    + destruct IHM with i.
      assert ({A' | cs_nTy nTy5 i A'})
        as [ ]
          by (apply cs_nTy_dec).

      eexists; constructor; eauto.
    + destruct IHM1 with i.
      destruct IHM2 with i.
      eexists; constructor; eauto.

    + admit. (* mvar, assumptions *)
Qed.

Lemma cs_nK_dec:
  forall (L : nK) (i : Ixc),
    { L' : nK | cs_nK L i L' }.
Proof.
  intros.
  induction L.
  eexists.
  econstructor.
  destruct IHL.
  assert ({nTy5' : nTy | cs_nTy nTy5 i nTy5'}) by (apply cs_nTy_dec).
  destruct H.
  eexists.
  econstructor; eauto.
Qed.

Lemma cs_nctx_dec:
  forall (G : nctx) (i : Ixc) (A : nTy),
    (i <= length G) -> 
    { G' : nctx | cs_nctx G i A G' }.
Proof.
  intros.
  generalize dependent A.
  generalize dependent i.
  induction G.
  - (* nil case *)
    intros.
    destruct i.
    + eexists; constructor.
    + exfalso.
      inversion H.
  - (* cons case *)   
    intro i.
    generalize dependent a.
    generalize dependent G.
    induction i.

    + intros.
      assert ({G' : nctx | cs_nctx G 0 a G'})
        by (apply IHG; auto with arith).
      destruct H0.
      
      assert ({A' : nTy | cs_nTy A 0 A'}) by (apply cs_nTy_dec).
      destruct H0.
      
      eexists; econstructor; eauto.
      
    + intros.   
      
      assert ( {G' : nctx | cs_nctx G i A G'})
        by (eapply IHG; auto with arith).
      destruct H0.

      assert ({a' : nTy | cs_nTy a i a'}) by (apply cs_nTy_dec).
      destruct H0.
      
      eexists; econstructor; eauto.
Qed.

(* * decidability of context shifting **)

Lemma cs_nTy_dec_inverse:
  forall (A' : nTy) (i : Ixc),
    { A : nTy | cs_nTy A i A' } + { forall A : nTy, ~ cs_nTy A i A'}
with cs_nte_dec_inverse:
  forall (M' : nte) (i : Ixc),
    {  M : nte | cs_nte M i M' } + { forall M : nte, ~ cs_nte M i M'}.
Proof.
  intros.
  induction A'.
  left; eexists; constructor.
  
  destruct IHA'1; destruct IHA'2.
  destruct s; destruct s0.
  left; eexists; constructor; eauto.
  right; intros; intro.
  inversion H.
  eapply n; eauto.
  right; intros; intro.
  inversion H.
  eapply n; eauto.
  right; intros; intro.
  inversion H.
  eapply n; eauto.
  
  destruct IHA'.
  destruct s.
  assert ({M | cs_nte M i nte5 } + {forall M, ~ cs_nte M i nte5}) by (apply cs_nte_dec_inverse).
  destruct H.
  destruct s.
  left; eexists; constructor; eauto.
  right; intros; intro.
  inversion H.
  eapply n; eauto.
  right; intros; intro.
  inversion H.
  eapply n; eauto.
  
  (* lemma 2 *)
  intros.
  induction M'.
  left; eexists; constructor.
  (* case ixc *)

  assert ({ixc < i} + {ixc = i} + { i < ixc}) by (apply lt_eq_lt_dec).
  destruct H.
  destruct s.

  (* (ixc < i)  *)
  left.
  exists (termstar_nl_ixc ixc).
  generalize dependent ixc.
  induction i.
  intros.
  inversion l.
  intros.
  destruct ixc.
  constructor.
  eapply cs_nte_ixc_succ.
  apply IHi.
  apply lt_S_n; auto.

  (* (i = ixc)  *)
  rewrite e.
  clear e. clear ixc.
  right.
  induction i.
  intros.
  intro.
  inversion H.
  intros.
  intro.
  inversion H.
  eapply IHi; eauto.
 
  (* (i < ixc) *)
  destruct ixc.
  apply lt_le_S in l.
  apply le_n_0_eq in l.
  inversion l.
  left.
  exists (termstar_nl_ixc ixc).
  generalize dependent ixc.
  induction i.
  intros.
  constructor.
  intros.

  destruct ixc.
  apply lt_n_Sm_le in l.
  apply le_n_0_eq in l.
  inversion l.
  constructor.
  apply IHi.
  apply lt_S_n; auto.

  (* ixt *)
  left.
  exists (termstar_nl_ixt ixt).
  constructor.
  (* pi intro *)
  destruct IHM'.
  destruct s.
  assert ({A' | cs_nTy A' i nTy5 } + {forall A' , ~ cs_nTy A' i nTy5} ) by (apply cs_nTy_dec_inverse).
  destruct H.
  destruct s.
  left.
  exists (termstar_nl_pi_intro x0 x).
  constructor; eauto.

  right.
  intros; intro.
  inversion H.
  eapply n; eauto.

  right.
  intros; intro.
  inversion H.
  eapply n; eauto.
  
  destruct IHM'1.
  destruct s.
  destruct IHM'2.
  destruct s.
  left.
  exists (termstar_nl_pi_elim x x0).
  apply cs_nte_pi_elim; auto.

  right.
  intros; intro.
  inversion H.
  eapply n; eauto.

  right.
  intros; intro.
  inversion H.
  eapply n; eauto.
Qed.


(** determinacy of context shifting **)

Lemma cs_nTy_determinacy:
  forall (A B1 B2 : nTy) (i : Ixc),
    cs_nTy A i B1 -> cs_nTy A i B2 ->
    B1 = B2           
with cs_nte_determinacy:
  forall (M N1 N2 : nte) (i : Ixc),
    cs_nte M i N1 -> cs_nte M i N2 ->
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
  intros.
  inversion H0.

  assert (termstar_nl_ixc ixc'' = termstar_nl_ixc ixc''0).
  apply IHcs_nte; auto.
  f_equal; f_equal.
  inversion H5; auto.

  intros.
  inversion H0; auto.

  intros.
  inversion H1.
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
  forall (G G1 G2 : nctx) (A : nTy) (i : Ixc),
    cs_nctx G i A G1 -> cs_nctx G i A G2 ->
    G1 = G2.
Proof.
  intros.
  generalize dependent G2.
  induction H.

  - intros.
    inversion H0; constructor.
  - intros.
    inversion H1; f_equal.
    eapply cs_nTy_determinacy; eauto.
    eapply IHcs_nctx; eauto.
  - intros.
    inversion H1; f_equal; eauto using cs_nTy_determinacy.
Qed.

(** surjectivity of context shifting **)

Lemma cs_nTy_surjectivity:
  forall (A1 A2 B : nTy) (i : Ixc),
    cs_nTy A1 i B -> cs_nTy A2 i B ->
    A1 = A2           
with cs_nte_surjectivity:
  forall (M1 M2 N : nte) (i : Ixc),
    cs_nte M1 i N -> cs_nte M2 i N ->
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
  inversion H0.
  assert (termstar_nl_ixc  ixc = termstar_nl_ixc ixc0).
  apply IHcs_nte; auto.
  inversion H5.
  f_equal; auto.

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

(** context shifting composes **)
  
Fixpoint cs_nTy_cs (A A' B B' : nTy) (i : Ixc) (H : cs_nTy A i B) {struct H}:
    cs_nTy B 0 B' -> cs_nTy A 0 A' ->
    cs_nTy A' (S i) B'
with cs_nte_cs (M M' N N' : nte) (i : Ixc) (H : cs_nte M i N) {struct H}:
    cs_nte N 0 N' -> cs_nte M 0 M' ->
    cs_nte M' (S i) N'.
Proof.
  (* lemma 1 *)
  intros.
  generalize dependent B'.
  generalize dependent A'.
  induction H.

  intros.
  inversion H0; inversion H1.
  constructor.

  intros.
  inversion H1; inversion H2.
  constructor.
  apply IHcs_nTy1; auto.
  apply IHcs_nTy2; auto.

  intros.
  inversion H1; inversion H2.
  constructor.
  apply IHcs_nTy; auto.
  eapply cs_nte_cs; eauto.
  
  (* lemma 2 *)
  intros.
  generalize dependent N'.
  generalize dependent M'.
  induction H.

  intros.
  inversion H0; inversion H1.
  constructor.

  intros.
  inversion H0; inversion H1.
  constructor.
  eapply cs_nte_ixc_gt.

  intros.
  inversion H0; inversion H1.
  constructor.
  constructor.
    
  intros.
  inversion H0; inversion H1.
  constructor.
  apply IHcs_nte; constructor.

  intros.
  inversion H0; inversion H1.
  constructor.

  intros.
  inversion H1; inversion H2.
  constructor.
  eapply cs_nTy_cs; eauto.
  apply IHcs_nte; auto.

  intros.
  inversion H1; inversion H2.  
  constructor.
  apply IHcs_nte1; auto.
  apply IHcs_nte2; auto.
Qed.

(** cstu preservers cs **)

Fixpoint cs_nTy_cstu (B C B' C' : nTy) (i : Ixc) (H : cs_nTy B i C) {struct H}:
      cstu_nTy B 0 B' -> cstu_nTy C 0 C' ->
      cs_nTy B' (S i) C'
with cs_nte_cstu (M N M' N' : nte) (i : Ixc) (H : cs_nte M i N) {struct H}:
      cstu_nte M 0 M' -> cstu_nte N 0 N' ->
      cs_nte M' (S i) N'.
Proof.
  -  (* Lemma 1 *)
    intros.
    generalize dependent C'.
    generalize dependent B'.
    (* generalize dependent j.*)
    induction H.
    + (* tcon *)
      intros.
      inversion H0; inversion H1.      
      constructor.
    +  (* pi_intro *)
      intros.
      inversion H1; inversion H2.
      apply cs_nTy_pi_intro.
      eapply IHcs_nTy1; eauto.
      eapply IHcs_nTy2; eauto.
    + (* pi_elim *)
      intros.
      inversion H1; inversion H2.
      apply cs_nTy_pi_elim.
      eapply IHcs_nTy; eauto.
      eapply cs_nte_cstu; eauto.
  - (* Lemma 2 *)
    intros.
    generalize dependent N'.
    generalize dependent M'.
    (* generalize dependent i. *)
    induction H.
    +  (* con *)
      intros.
      inversion H0; inversion H1.
      constructor.
    +  (* ixc S *)
      intros.
      inversion H0; inversion H1.
      constructor.
      constructor.
    +  (* ixc 0 S S *)
      intros. 
      inversion H0; inversion H1.
      constructor.
      constructor.
    + (* ixc S ixc ~ S ixc' *)
      intros.
      inversion H0; inversion H1.
      constructor.
      eapply IHcs_nte.
      econstructor.
      econstructor.
    + (* ixt *)
      intros.
      destruct ixt.
      * inversion H0; inversion H1.
        (*generalize dependent j.*)
        generalize dependent N'.
        generalize dependent M'.
        induction ixc.
        { 
          intros.
          constructor.
        }
        {
          intros.
          constructor.
        }
      *  (* S ixt *)
        inversion H0; inversion H1.
        constructor.
    +  (* pi_intro *)
      intros.
      inversion H1; inversion H2.
      constructor.
      eapply cs_nTy_cstu; eauto.
      eapply IHcs_nte; eauto.
    +  (* pi_elim *)
      intros.
      inversion H1; inversion H2.
      constructor.
      eapply IHcs_nte1; eauto.
      eapply IHcs_nte2; eauto.
Defined.


(** tuts preservers cs **)


Fixpoint cs_nTy_tuts (B C B' C' : nTy) (M M' : nte) (i : Ixc) (H : cs_nTy B i C) {struct H}:
      cs_nte M i M' -> tuts_nTy B M B' -> tuts_nTy C M' C' -> 
      cs_nTy B' i C'
with cs_nte_tuts (M N M' N' P P' : nte) (i : Ixc) (H : cs_nte M i N)  {struct H}:
      cs_nte P i P' -> tuts_nte M P M' -> tuts_nte N P' N' ->
      cs_nte M' i N'.
Proof.
  (* Lemma 1 *)
  intros.
  generalize dependent C'.
  generalize dependent B'.
  induction H.
  (* tcon *)
  intros.
  inversion H1; inversion H2.
  constructor.
  (* pi_intro *)
  intros.
  inversion H2; inversion H3.
  apply cs_nTy_pi_intro.
  apply IHcs_nTy1; auto.
  apply IHcs_nTy2; auto.
  (* pi_elim *)
  intros.
  inversion H2; inversion H3.
  apply cs_nTy_pi_elim.
  apply IHcs_nTy; auto.
  eapply cs_nte_tuts.
  exact H1.
  exact H0.
  exact H9.
  exact H15.

  (* Lemma 2 *)
  intros.
  generalize dependent N'.
  generalize dependent M'.
  (* generalize dependent i. *)
  induction H.
  (* con *)
  intros.
  inversion H1; inversion H2.
  apply cs_nte_con.
  (* ixc S *)
  intros.
  inversion H1; inversion H2.
  constructor.
  (* ixc 0 S S *)
  intros. 
  inversion H1.
  inversion H2.
  constructor.

  intros.
  inversion H1.
  inversion H2.
  constructor.
  auto.
  
  (* ixt *)
  intros.
  destruct ixt.
  
  inversion H1; inversion H2.
  rewrite <- H4; rewrite <- H6; auto.

  inversion H1; inversion H2.
  constructor.

  (* pi_intro *)
  intros.
  inversion H2; inversion H3.
  apply cs_nte_pi_intro.
  eapply cs_nTy_tuts; eauto.
  eapply IHcs_nte; eauto.
  (* pi_elim *)
  intros.
  inversion H2; inversion H3.
  eapply cs_nte_pi_elim.
  eapply IHcs_nte1; eauto.
  eapply IHcs_nte2; eauto.
Defined.

(** context shifting preserves context shifting in simple context **)

Lemma cs_snctx_cs:
  forall (sG sG' : snctx) (i : Ixc) (tau tau' : snTy),
    cs_snctx sG i tau' sG' ->
    cs_snctx (tau :: sG) (S i) tau' (tau :: sG').
Proof.  
  intros.
  generalize dependent tau.
  induction H.
  intros.
  constructor.
  intros.
  constructor.
  intros.
  constructor.
  constructor.
  exact H.
  intros.
  constructor.
  apply IHcs_snctx.
Qed.

(** context shifting prepends for zeroc **)

Lemma cs_snctx_zeroc:
  forall (sG sG' : snctx) (tau : snTy),
    cs_snctx sG 0 tau sG' ->
    sG' = tau :: sG.
Proof.
  intros.
  generalize dependent sG'.
  generalize dependent tau.
  induction sG.
  intros.
  inversion H; auto.

  intros.
  inversion H.
  f_equal.
  apply IHsG; auto.
Qed.  

(** context shifting generalised constructors **)
Lemma cs_snctx_var:
  forall (sG : snctx) (tau : snTy),
    cs_snctx sG 0 tau (tau :: sG). 
Proof.
  induction sG.
  intros; constructor.
  intros.
  constructor.
  apply IHsG.
Qed.

(**
   * Context unshifting
 **)

(** decidability of context unshifting **)

Lemma cu_nTy_dec:
  forall (A : nTy) (i : Ixc),
    { A' : nTy | cu_nTy A i A' } + {forall (A' : nTy), ~ cu_nTy A i A'}
with cu_nte_dec:
  forall (M : nte) (i : Ixc),
    {  M' : nte | cu_nte M i M' } + {forall (M' : nte), ~ cu_nte M i M'}.
Proof.
  { (* lemma 1 *)
    intros.
    induction A as [ a | A IH_A B IH_B | A IH_A M ].
    - left.
      eexists; constructor.
    - destruct IH_A as [ [A'] | ].
      + destruct IH_B as [ [B'] | ].
        * left; eexists; constructor; eauto.
        *  right; intros; intro.
           inversion H.
           eapply n; eauto.
      + right; intros; intro.
        inversion H.
        eapply n; eauto.
    - destruct IH_A as [ [A'] | ].
      + assert (H_M : {M' : nte | cu_nte M i M'} +
                      {(forall M' : nte, ~ cu_nte M i M')})
          by (apply cu_nte_dec).
        destruct H_M as [ [M'] | ].
        * left; eexists; constructor; eauto.        
        * right; intros; intro.
          inversion H.
          eapply n; eauto.
      + right; intros; intro.
        inversion H.
        eapply n; eauto.
  }
  { (* lemma 2 *) 
    intros.
    induction M as [ a |  | | A M | M IH_M N IH_N ].
    - intros; left.
      eexists; econstructor.
    - generalize dependent ixc.
      induction i.
      + intros.
        destruct ixc.
        * right; intros; intro.
          inversion H.
        * left; eexists; constructor.
      + intros.
        destruct ixc.
        * left; eexists; constructor.
        * assert ({M' : nte | cu_nte (termstar_nl_ixc ixc) i M'} +
                  {(forall M' : nte, ~ cu_nte (termstar_nl_ixc ixc) i M')}) 
            by (eapply IHi).
          destruct H as [ [M'] | ].
          { destruct M'.
            - exfalso; inversion c.
            - left; eexists; constructor; eauto.
            - exfalso; inversion c.
            - exfalso; inversion c.
            - exfalso; inversion c.
          }
          { right; intro; intro.
            inversion H.
            eapply n; eauto.
          }
    - destruct ixt.
      + left; eexists; constructor.
      + left; eexists; constructor.
    - destruct IHM as [ [M'] | ].
      + assert ({A' : nTy | cu_nTy A i A'} +
                {(forall A' : nTy, ~ cu_nTy A i A')})
          by (apply cu_nTy_dec).
        destruct H as [ [A'] | ].
        * left; eexists; constructor; eauto.
        * right; intros; intro.
          inversion H.
          eapply n; eauto.
      + right; intros; intro.
        inversion H.
        eapply n; eauto.
    - destruct IH_M as [ [M'] | ].
      destruct IH_N as [ [N'] | ].
      + left; eexists; constructor; eauto.
      + right; intros; intro.
        inversion H.
        eapply n; eauto.
      + right; intros; intro.
        inversion H.
        eapply n; eauto.
  }
Qed.              

Lemma cu_nctx_dec:
  forall (G : nctx)  (i : Ixc),
    { G'A' : nctx * nTy | cu_nctx G i (fst G'A') (snd G'A')  }
    + {forall (A' : nTy) (G' : nctx), ~ cu_nctx G i G' A'}.
Proof.                                       
  intros.
  generalize dependent G.
  induction i.
  - intros.
    induction G.
    + right; intros; intro.
      inversion H.
    + destruct IHG as [ [ [ ?G' ?A' ] ] | ].
      * assert ({a' | cu_nTy a 0 a'} + {forall a', ~ cu_nTy a 0 a'})
          by (apply cu_nTy_dec).
        destruct H as [ [a'] | ].
        { left.
          exists (A' :: G', a').
          apply cu_nctx_var_zeroc; auto. }
        { right; intros; intro.
          cbn in c.
          inversion H.
          rewrite <- H2 in c; inversion c.
          eapply n; eauto. }
      * destruct G.
        { left; exists (nil, a).
          cbn.
          constructor. }
        { right; intros; intro.
          inversion H.
          eapply n; eauto. }
  - intros.
    induction G.
    + intros.
      right; intros; intro.
      inversion H.
    + intros.
      assert ({G'A' : nctx * nTy | cu_nctx G i (fst G'A') (snd G'A')} +
              {(forall (A' : nTy) (G' : nctx), ~ cu_nctx G i G' A')})
             by (apply IHi).
      destruct H as [ [ [?G' ?A' ]  w  ] | ].
      *  cbn in w.

         assert ({a' | cu_nTy a i a'} + {forall a', ~ cu_nTy a i a'})
           by (apply cu_nTy_dec).
         destruct H as [[a'] | ].

         { left.
           exists (a' :: G' , A').
           constructor; auto. }
         { right; intros; intro.
           inversion H.
           eapply n; eauto. }
      * right; intros; intro.
        inversion H.
        eapply n; eauto.
Qed.

Lemma cu_nctx_wf_dec:
  forall (S : nsgn) (G : nctx) (i : Ixc),
    wfctx_nl S G -> i < length G ->
    { G'A' : nctx * nTy | cu_nctx G i (fst G'A') (snd G'A')  }.
Proof.                                       
  intros.
  generalize dependent G.
  induction i.
  - intro G.
    remember (length G).
    generalize dependent G.
    induction n; intros G Heq HwfG HlG. (* induction on length G! *)
    + exfalso.
      inversion HlG.
    + destruct G as [ | B ].
      * inversion Heq.
      * assert ({B' | cu_nTy B 0 B'})
        as [ B' ]
          by (admit). (* from wf? *)

        destruct G.
        
        { (* ctx = A :: nil *)
          exists (nil, B).
          cbn.
          apply cu_nctx_empty. }
          
      * destruct IHG as [ [ ?G' ?A' ]  ].
        { admit. (* induction on length G! *) }
        { cbn; auto with arith. }

        cbn in c0.
        exists (A' :: G', a').
        cbn.
        apply cu_nctx_var_zeroc; auto.

  - intros.
    induction G. (* length G *)
    + intros.
      exfalso. 
      inversion H0.
    + intros.
      assert ({G'A' : nctx * nTy | cu_nctx G i (fst G'A') (snd G'A')})
        as [ [ ?G' ?A' ] w ].

      apply IHi.
      admit. (* induction on length G *)
      auto with arith.
      
      *  cbn in w.

         assert ({a' | cu_nTy a i a'})
           as [ a' ]
             by (admit).

         exists (a' :: G', A').
         constructor; auto.

Qed.

(** determinacy of context unshifting **)

Fixpoint cu_nTy_determinacy (A B1 B2 : nTy) (i : Ixc)
         (H : cu_nTy A i B1) {struct H}:
  cu_nTy A i B2 -> B1 = B2           
with cu_nte_determinacy (M N1 N2 : nte) (i : Ixc)
                        (H :  cu_nte M i N1) {struct H}:
       cu_nte M i N2 -> N1 = N2.
Proof.
  (* lemma 1 *)
  - intros.
    generalize dependent B2.
    induction H.
    + intros.
      inversion H0; auto.
    + intros.
      inversion H1.
      f_equal; eauto using IHcu_nTy1 , IHcu_nTy2.
    + intros.
      inversion H1.
      f_equal; eauto using IHcu_nTy , cu_nte_determinacy.
  - intros.
    generalize dependent N2.
    induction H.
    + intros.
      inversion H0; auto.
    + intros.
      inversion H0; auto.
    + intros.
      inversion H0; auto.
    + intros.
      inversion H0.
      assert (termstar_nl_ixc ixc'' = termstar_nl_ixc ixc''0)
        by (eauto using IHcu_nte).
      inversion H5.
      rewrite <- H7; auto.
    + destruct ixt.
      * intros.
        inversion H0; auto.
      * intros.
        inversion H0; auto.
    + intros.
      inversion H1.
      f_equal; eauto using IHcu_nte, cu_nTy_determinacy.
    + intros.
      inversion H1.
      f_equal; eauto using IHcu_nte1, IHcu_nte2.
Qed.

Lemma cu_nctx_determinacy:
  forall (G G1 G2 : nctx) (A1 A2 : nTy) (i : Ixc),
    cu_nctx G i G1 A1 -> cu_nctx G i G2 A2 ->
    G1 = G2 /\ A1 = A2.
Proof.
  intros.
  generalize dependent G.
  generalize dependent G1.
  generalize dependent G2.
  generalize dependent A1.
  generalize dependent A2.
  induction i.
  - intros.
    generalize dependent G1.
    generalize dependent G2.
    generalize dependent A1.
    generalize dependent A2.
    induction G.
    + intros.
      inversion H.
    + intros.
      inversion H.
      * rewrite <- H3 in H0.
        inversion H0.
        rewrite H4 in H8.
        split; auto.
        inversion H8.
      * inversion H0.
        rewrite <- H9 in H4; inversion H4.
        split.
        f_equal; eapply IHG; eauto.
        eapply cu_nTy_determinacy; eauto.
  - intros.
    inversion H.
    inversion H0.
    rewrite <- H3 in H9; inversion H9.
    rewrite H14 in H10.
    rewrite H15 in H8.
    split.
    f_equal.
    eapply cu_nTy_determinacy; eauto.
    eapply IHi; eauto.   
    eapply IHi; eauto.
Qed.
  
(** context unshifting is an inversion of context shifting **)

Lemma cu_nTy_inverse_cs:
  forall (A A' : nTy) {i : Ixc},
    cs_nTy A i A' -> cu_nTy A' i A
with cu_nte_inverse_cs:
  forall (M M' : nte) {i : Ixc},
    cs_nte M i M' -> cu_nte M' i M.
Proof.
  { (* lemma 1 *)
    intros.
    induction H.
    - constructor.
    - constructor; auto.
    - constructor; auto.
  }
  {
  (* lemma 2 *)
    intros.
    induction H.
    - constructor.
    - constructor.
    - constructor.
    - constructor.
      apply IHcs_nte.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
  }
Qed.


Lemma cu_nctx_inverse_cs:
  forall (G G' : nctx) (A : nTy) (i : Ixc),
    cs_nctx G i A G' -> cu_nctx G' i G A.
Proof.
  intros.
  generalize dependent A.
  generalize dependent G.
  generalize dependent i.
  induction G'.
  - intros.
    inversion H.
  - intros.
    generalize dependent G.
    generalize dependent A.
    induction i.
    + intros.
      inversion H.
      * econstructor.
      * constructor.
        apply cu_nTy_inverse_cs; auto.
        apply IHG'; auto.
    + intros.
      inversion H.
      apply cu_nctx_var_succ.
      apply IHG'; auto.
      apply cu_nTy_inverse_cs; auto.
Qed.  


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
(*
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
*)

(**
   * Context-unshifitng type-shifting
**)

(** decidability of cuts **)

Lemma cuts_nTy_dec:
  forall (A : nTy),
    { A' | cuts_nTy A A' }
with cuts_nte_dec:
  forall (M : nte),
    { M' | cuts_nte M M' }.
Proof.
  - (* lemma 1 *)
    intros.
    induction A as [ a | A [ A' ]  B [ B' ] | A [ A' ] M ].
    + eexists; constructor.
    + eexists; constructor; eauto.
    + assert ({M' | cuts_nte M M'}) as [ M' ]
        by (apply cuts_nte_dec).
      eexists; constructor; eauto.
  - (* lemma 2 *)
    intros.
    induction M as [ c | |  | A M [M'] | M1 [M1'] M2 [M2'] ].
    + eexists; constructor.
    + destruct ixc.
      * eexists; constructor.
      * eexists; constructor.
    + eexists; constructor.
    + assert ({A' | cuts_nTy A A'}) as [ A' ]
          by (apply cuts_nTy_dec).
      eexists; constructor; eauto.
    + eexists; constructor; eauto.
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
    { A' | tuts_nTy A N A' }
with tuts_nte_dec:
  forall (M N : nte),
    { M' | tuts_nte M N M' }.
Proof.
  intros.
  induction A.
  exists (typestar_nl_tcon tcon5).
  trivial using tuts_nTy_tcon.
  destruct IHA1.
  destruct IHA2.
  exists (typestar_nl_pi_intro x x0).
  auto using tuts_nTy_pi_intro.
  (* next case *)
  destruct IHA.
  assert ({M' | tuts_nte nte5 N M'}) by (apply tuts_nte_dec).
  destruct H.
  exists (typestar_nl_pi_elim x x0).
  auto using tuts_nTy_pi_elim.

  (* lemma tuts_nte_dec *)
  intros.
  induction M.
  (* case con *)
  exists (termstar_nl_con con5).
  auto using tuts_nte_con.
  (* case ixc *)
  exists (termstar_nl_ixc (ixc)).
  apply tuts_nte_ixc.
  (* case ixt *)
  destruct ixt.
  exists N.
  apply tuts_nte_ixt_zero.
  exists (termstar_nl_ixt ixt).
  apply tuts_nte_ixt_succ.
  (* case pi_intro *)  
  destruct IHM.
  assert ({A' | tuts_nTy nTy5 N A'}) by (apply tuts_nTy_dec).
  destruct H.
  exists (termstar_nl_pi_intro x0 x).
  auto using tuts_nte_pi_intro.
  (* case pi elim *)
  destruct IHM1.
  destruct IHM2.
  exists (termstar_nl_pi_elim x x0).
  auto using tuts_nte_pi_elim.
Qed.

Lemma tuts_nK_dec:
  forall (L : nK) (N : nte) ,
    { L' | tuts_nK L N L' }.
Proof.
  intros.
  induction L as [ | A ] .
  - eexists; constructor.
  - destruct IHL as [ L' ].
    assert ({A' | tuts_nTy A N A'})
      by (apply tuts_nTy_dec).
    destruct H as [ A' ].
    eexists; constructor; eauto.
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

Lemma tuts_nK_determinacy:
  forall (L L1 L2: nK) (N : nte),
    tuts_nK L N L1 -> tuts_nK L N L2 ->
    L1 = L2.
Proof.
  intros.
  generalize dependent L2.
  induction H.
  intros.
  inversion H0; auto.
  intros.
  inversion H1.
  f_equal.
  eapply tuts_nTy_determinacy; eauto.
  eapply IHtuts_nK; eauto.
Qed.  

(** context shifting preserves tuts **)

Fixpoint tuts_nTy_cs (A B A' B': nTy) (N N' : nte) (H : tuts_nTy A N B) (i : Ixc) {struct H}:
    cs_nTy A i A' -> cs_nTy B i B' -> cs_nte N i N' -> tuts_nTy A' N' B'
with tuts_nte_cs (M M' N csM csM' csN : nte) (H : tuts_nte M N M') (i : Ixc) {struct H}:
    cs_nte M i csM -> cs_nte M' i csM' -> cs_nte N i csN -> tuts_nte csM csN csM'.
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
  generalize dependent i.
  induction H.
  (* con *)
  intros; inversion H0; inversion H1; constructor.
  (* ixc *)
  intros.

  inversion H0.
  rewrite <- H4 in H1.
  inversion H1.
  constructor.

  rewrite <- H4 in H1.
  inversion H1.
  constructor.

  rewrite <- H3 in H; inversion H.

  rewrite <- H4 in H1; inversion H1.
  rewrite <- H in H7; inversion H7.

  destruct ixc; inversion H; inversion H6.
  rewrite H11 in H3.
  rewrite H12 in H8.

  assert (termstar_nl_ixc ixc'' = termstar_nl_ixc ixc''0).
  eapply cs_nte_determinacy; eauto.
  inversion H10.
  constructor.
  
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
  eapply IHtuts_nte; eauto.
  (* pi elim case *)
  intros; inversion H1; inversion H2; constructor.
  eapply IHtuts_nte1; eauto.
  eapply IHtuts_nte2; eauto.
Defined.

(** context shifting preserves tuts in inverse **)


Fixpoint tuts_nTy_cs_inverse (nA nA' A A' : nTy) (nN N : nte) (H : tuts_nTy nA nN nA') (i : Ixc) {struct H}:
  cs_nTy A i nA -> cs_nte N i nN -> cs_nTy A' i nA' -> tuts_nTy A N A'
with tuts_nte_cs_inverse (nM nM' nN M N M' : nte) (H : tuts_nte nM nN nM') (i : Ixc) {struct H}:
       cs_nte M i nM -> cs_nte N i nN -> cs_nte M' i nM' ->    tuts_nte M N M'.
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
  generalize dependent i.
  induction H.
  intros.
  inversion H0; inversion H2.
  constructor.
  intros.

  inversion H0.
  rewrite <- H3 in H2; inversion H2.
  rewrite <- H5 in H6; inversion H6.
  constructor.

  rewrite <- H3 in H2; rewrite <- H5 in H2; inversion H2.
  constructor.

  rewrite <- H4 in H2; rewrite <- H in H2; inversion H2.
  assert (termstar_nl_ixc ixc0 = termstar_nl_ixc ixc1) by (eapply cs_nte_surjectivity; eauto).
  inversion H10.
  constructor.

  (* ixt *)
  intros.
  inversion H0.
  assert (N = M').
  eapply cs_nte_surjectivity; eauto.
  rewrite H4.
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
