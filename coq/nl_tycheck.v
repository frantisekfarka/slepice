Require Import List.

Require Import defns.
Require Import nl_fusion.
Require Import nl_sgn.
Require Import nl_eq.
Require Import nl_struct.

Require Import nl_walgeq.


(** 
    context shifting preservers well-formedness of context

    proof by induction on length of the context

 **)

Lemma wfctx_nl_cs:
  forall (S : nsgn) (G G' : nctx) (A : nTy),
    wfctx_nl S G ->
    cs_nctx G 0 A G' ->
    wftype_nl S G A kindstar_nl_type ->
    wfctx_nl S G'.
Proof.
  intros S [ | G ].
  - intros.
    inversion H0.
    econstructor; eauto.
    + constructor.
  - intros.
    inversion H0.
    econstructor; eauto.
    + constructor; eauto using cu_nTy_inverse_cs, cu_nctx_inverse_cs.
Qed.

(**
    erasure preservers well-formedness of signature
**)

Lemma wfsig_nl_erasure:
  forall (S : nsgn),
    wfsig_nl S -> wfssig_nl (erasure_nsgn S).
Proof.
  intros S HwfS.
  induction HwfS.
  - cbn; constructor.
  - cbn; constructor.
    auto.
    
    intro Hc; eapply H0.
    apply indomsnTCon_stable; auto.

  - cbn; constructor.
    auto.

    intro; eapply H0.
    apply indomsnCon_stable; auto.
Qed.


(**
    * determinacy of wftype
**)

Lemma wftype_nl_determinacy:
  forall (S : nsgn) (G : nctx) (sA : sTy) (A : nTy) (L1 L2 : nK),
    sA = struct_nTy A ->
    wfsig_nl S -> wfctx_nl S G ->
    wftype_nl S G A L1 ->
    wftype_nl S G A L2 ->
    L1 = L2.
Proof.
  intros S G sA A L1 L2 Hstruct HwfS.
  generalize dependent L1.
  generalize dependent L2.
  generalize dependent G.
  generalize dependent A.
  induction sA;
    intros A Hstruct G L1 L2 Hwfctx HwfTy1 HwfTy2.
  -  (* leaf *)      
    inversion HwfTy1.
    + rewrite <- H3 in HwfTy2; inversion HwfTy2.
      eauto using boundnTCon_determinacy.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
  -  (* pi intro *)
    inversion HwfTy1.
    + rewrite <- H3 in Hstruct; inversion Hstruct.
    + rewrite <- H5 in HwfTy2; inversion HwfTy2.
      auto.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
  - (* elim *)
    inversion HwfTy1.
    + rewrite <- H3 in Hstruct; inversion Hstruct.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
    + rewrite <- H5 in Hstruct; inversion Hstruct.
      rewrite <- H5 in HwfTy2; inversion HwfTy2.
      assert ((kindstar_nl_pi_intro nB' nL)
              = (kindstar_nl_pi_intro nB'0 nL0))
        by (eauto using IHsA).
      inversion H18.
      rewrite <- H21 in H17.
      eauto using tuts_nK_determinacy.
Qed.  

Lemma wfterm_nl_determinacy:
  forall (S : nsgn) (G : nctx) (sM : ste) (M : nte) (A1 A2 : nTy),
    wfsig_nl S -> wfctx_nl S G ->
    sM = struct_nte M ->
    wfterm_nl S G M A1 ->
    wfterm_nl S G M A2 ->
    A1 = A2.
Proof.
  intros.
  generalize dependent A2.
  generalize dependent A1.
  generalize dependent M.
  generalize dependent G.
  induction sM.
  intros.
  - destruct M as [ c | | | | ] ; inversion H1.
    + inversion H2.
      inversion H3.
      eauto using boundnCon_determinacy.
    + clear H1.
      generalize dependent G.
      generalize dependent A1.
      generalize dependent A2.
      induction ixc.
      * intros.
        inversion H2.
        inversion H3.
        rewrite <- H9 in H5; inversion H5.
        eauto using eq_trans.
      * intros.
        inversion H2.
        rewrite <- H7 in H3.
        inversion H3.
        rewrite <- H7 in H0.
        inversion H0.
        assert (nctx' = nctx'0 /\ nB' = nB'0)
          by (eauto using cu_nctx_determinacy).
        inversion H24.
        assert (nctx'1 = nctx'0)
          by (eapply cu_nctx_determinacy; eauto).
        assert (nA = nA0).
        (* rewrite H19 in H5. *)
        eapply IHixc. 
        rewrite H27 in H22.
        exact H22.
        rewrite <- H25.
        exact H5.
        exact H15.
        rewrite <- H28 in H17.
        eauto using cs_nTy_determinacy, eq_trans.
    + inversion H2.
  - intros.
    destruct M; inversion H1.

    inversion H2.
    inversion H3.

    assert (nctx' = nctx'0) by (eauto using cs_nctx_determinacy).
    rewrite <- H26 in H23.
    assert (nM2' = nM2'0) by (eauto using cstu_nte_determinacy).

    
    assert (nA2 = nA3).
    eapply IHsM.
    rewrite <- H26 in H19.
    eapply wfctx_nl_cs; eauto.
    rewrite H6.
    eapply struct_nte_cstu; eauto.
    rewrite H27 in H13.
    exact H13.
    exact H23.

    rewrite <- H28 in H25.
    f_equal; eauto using cuts_nTy_determinacy.
  - intros.
    destruct M; inversion H1.

    inversion H2.
    inversion H3.
    
    assert (nA2 = nA3).
    eapply IHsM2; eauto.
    rewrite <- H24 in H23.
    eapply tuts_nTy_determinacy; eauto.
Qed.      
  

(**
    * wftype and wfterm decidability 
**)

Fixpoint wftype_nl_dec' (S : nsgn) (G : nctx)
         (sA : sTy) (A : nTy) {struct sA}:
    wfsig_nl S -> wfctx_nl S G ->
    sA = struct_nTy A ->
    { L | wftype_nl S G A L } +
    { forall L, ~ (wftype_nl S G A L)}
with wfterm_nl_dec' (S : nsgn) (G : nctx)
                   (sM : ste) (M : nte) {struct sM}:
    wfsig_nl S -> wfctx_nl S G ->
    sM = struct_nte M ->
    { A | wfterm_nl S G M A } +
    { forall A, ~ (wfterm_nl S G M A)}.
Proof.
  intros.
  generalize dependent A.
  generalize dependent G.
  induction sA.
  - (* struct ~ leaf *)
    intros.
    destruct A.
    + (* tcon *)
      assert ({ L | boundnTCon tcon5 L S } +
              { forall L, ~ (boundnTCon tcon5 L S)})
        by (apply boundnTCon_dec).
      destruct H2 as [ [L] | contra ].
      * (* boundnTCcon *)
        left; eexists; econstructor; eauto.
      * (* ~ not boundnTCon *)
          right; intros; intro Hwf; inversion Hwf.
          eapply contra; eauto.
    + (* pi intro on leaf *)
      inversion H1.
    + (* pi elim on leaf *)
      inversion H1.
  - (* struct step case pi_intro *)
  intros.
  destruct A.
  +  inversion H1.
  +  inversion H1.
     assert ({L | wftype_nl S G A1 L}
          + {forall L, ~ wftype_nl S G A1 L}).
     apply IHsA1.
     exact H0.
     exact H3.
     destruct H2 as [ [L] | contra ].
     * (* exists L *)
       assert ({L = kindstar_nl_type} + {L <> kindstar_nl_type})
         by (apply eq_nK).
     destruct H2.
     { (* L = type *)
       rewrite e in w.
       assert ({ G' | cs_nctx G 0 A1 G'})
         by (apply cs_nctx_dec; auto with arith).
       destruct H2 as [?G'].
       assert ({ A2' | cstu_nTy A2 0 A2'}) by (apply cstu_nTy_dec).
       destruct H2 as [ ?A2' ].
       assert ({L | wftype_nl S G' A2' L}
               + {forall L, ~ wftype_nl S G' A2' L}).
       {
         apply IHsA2.
         eapply wfctx_nl_cs; eauto.
         rewrite H4.
         eapply struct_nTy_cstu; eauto.
       }
       destruct H2 as [ [L2] | ].
       { 
         assert ({L2 = kindstar_nl_type} +
                 {L2 <> kindstar_nl_type}) by (apply eq_nK).
         destruct H2.
         { (* the valid subcase *)
           left.
           rewrite e0 in w0.
           eexists; econstructor; eauto.
         }
         {  (* L2 <> typeK case *)
           right; intros; intro HwfA2; inversion HwfA2.
           assert (A2' = nB') by (eapply cstu_nTy_determinacy; eauto).
           rewrite <- H13 in H12.
           assert (G' = nctx') by (eapply cs_nctx_determinacy; eauto).
           rewrite <- H14 in H12.
           
           assert (struct_nTy A2 = struct_nTy A2')
             by (eapply struct_nTy_cstu; eauto).
           rewrite H15 in H4.
           
           assert (L2 = kindstar_nl_type).
           eapply wftype_nl_determinacy.
           eauto.
           eauto.
           eapply wfctx_nl_cs. 
           exact H0.
           exact c.
           exact H6.
           exact w0.
           exact H12.
           apply n; auto.
         }
       }
       { (*  ~ wftype_nl S x0 x1 L *)
         right; intros; intro.
         inversion H2.
         eapply n.
         assert (A2' = nB') by (eapply cstu_nTy_determinacy; eauto).
         rewrite H14.
         assert (G' = nctx') by (eapply cs_nctx_determinacy; eauto).
         rewrite H15.
         eauto.
       }
     }
     { (* x <> type *)
       right; intros; intro.
       inversion H2.
       assert (L = kindstar_nl_type)
         by (clear H4; eapply wftype_nl_determinacy; eauto).
       apply n; auto.
     }
     * (* pi intro *)
       inversion H1.
       right; intros; intro.
       inversion H2.
       eapply contra; eauto.
  + inversion H1.
  - (* step case: pi elim *)
    intros.
    destruct A.
    + inversion H1.
    + inversion H1.
    + inversion H1.
      
      assert ( {L : nK | wftype_nl S G A L} +
           {(forall L : nK, ~ wftype_nl S G A L)}).
      apply IHsA; auto.
      destruct H2.
      * destruct s.
        destruct x.
        { (* case : wrong kind of A *)
          right; intros; intro.
          inversion H2.
          assert ( kindstar_nl_type =  (kindstar_nl_pi_intro nB' nL)).
          eapply wftype_nl_determinacy ; eauto.
          inversion H14. }
        { assert ({B : nTy | wfterm_nl S G nte5 B } +
                  {(forall B : nTy, ~ wfterm_nl S G nte5 B )}).
          
          eapply wfterm_nl_dec' with (sM := ste5).
          auto.
          auto.
          exact H4.
          
          destruct H2.
          { destruct s.
            assert ({x' | tuts_nK x nte5 x'}) by (apply tuts_nK_dec).
            destruct H2.
            assert ({walgeq_nl_Ty
                       (erasure_nsgn S) (erasure_nctx G)
                       x0 nTy5 skind_nl_type } +
                    { ~ walgeq_nl_Ty
                        (erasure_nsgn S) (erasure_nctx G)
                        x0 nTy5 skind_nl_type }).
            apply walgeq_nTy_check.
            auto.
            apply wfsig_nl_erasure; auto.
            destruct H2.
            left; exists x1.
            eapply ty_nl_pi_elim.
            exact w.
            exact w0.
            exact w1.
            exact t.

            right.
            intros; intro.
            inversion H2.
            assert (x0 = nB) by (eauto using wfterm_nl_determinacy).
            rewrite H14 in n.
            assert (kindstar_nl_pi_intro nTy5 x =
                    kindstar_nl_pi_intro nB' nL)
              by (eauto using wftype_nl_determinacy).
            inversion H15.
            rewrite H17 in n.
            eapply n; eauto.
          }
          { (* not wf B *)
            right; intros; intro.
            inversion H2.
            eapply n; eauto. } }
      * (* not wf A *)
        right; intros; intro.
        inversion H2.
        eapply n; eauto.

  (* mutual lemma *)

  - generalize dependent M. 
    generalize dependent G.
    induction sM.

    + (* leaf *)
      intros.
      destruct M as [ c | | | | ].
      * (* con *)
        assert ({ A | boundnCon c A S} + {forall A, ~ boundnCon c A S})
               by (apply boundnCon_dec).
        destruct H2.
        { destruct s as [ A' ].
          left; eexists; constructor; eauto. }
        { right; intros; intro; eapply n.
          inversion H2; eauto. }
      * (* ixc *)
        clear H1.
        generalize dependent G.
        induction ixc.
        { intros.
          destruct G.
          { right; intros; intro.
            inversion H1. }
          { left; eexists; econstructor; eauto. } }
        { destruct G.
          { right; intros; intro.
            inversion H1. }
          { intros.            
            assert ({ G'B' | cu_nctx (n :: G) 0 (fst G'B') (snd G'B')} +
                    {forall B' G', ~ cu_nctx (n :: G) 0 G' B'})
              by (apply cu_nctx_dec).
            destruct H1 as [ [[?G' ?B']] | ].
            - cbn in c.
              assert (wfctx_nl S G').
              inversion H0.
              assert (nctx' = G').
              eapply cu_nctx_determinacy; eauto.
              rewrite <- H7; auto.
              assert ({A : nTy | wfterm_nl S G' (termstar_nl_ixc ixc) A} +
                      {(forall A : nTy, ~ wfterm_nl S G' (termstar_nl_ixc ixc) A)})
                by (apply IHixc; auto).

              destruct H2 as [ [ A ] | ].
              + assert ({A' | cs_nTy A 0 A'}) by (apply cs_nTy_dec).
                destruct H2 as [ A' ].
                left; eexists.
                econstructor; eauto.
              + right; intros; intro.
                inversion H2.
                assert (nctx' = G').
                eapply cu_nctx_determinacy; eauto.
                rewrite H11 in H8.
                eapply n0; eauto.
            - right; intros; intro.
              inversion H1.
              eapply n0; eauto. } }
      * (* case ixt - not a w.f. term *)
        right; intro; intro.
        inversion H2.
      * inversion H1.
      * inversion H1.
    + intros.
      destruct M as [ | | | B M | ].
      * inversion H1.
      * inversion H1.
      * inversion H1.
      * inversion H1.
        assert ({L : nK | wftype_nl S G B L} +
                {(forall L : nK, ~ wftype_nl S G B L)}).
             
        eapply wftype_nl_dec' with (sA := sTy5).
        auto.
        auto.
        auto.
        
        destruct H2 as [ [L] | ].
        assert ({L = kindstar_nl_type} + {L <> kindstar_nl_type})
          by (apply eq_nK).
        destruct H2.
        rewrite e in w.
        assert ({G' | cs_nctx G 0 B G'})
          by (apply cs_nctx_dec; auto with arith).
        destruct H2 as [G'].
        assert (wfctx_nl S G').
        { destruct G'.
          inversion c.
          econstructor; eauto using cu_nctx_inverse_cs. }
        assert ({M' | cstu_nte M 0 M'}) by (apply cstu_nte_dec).
        destruct H5 as [ M' ].
        assert ({A : nTy | wfterm_nl S G' M' A} +
                {(forall A : nTy, ~ wfterm_nl S G' M' A)}).
        { apply IHsM; auto.
          rewrite H4; eauto using struct_nte_cstu. }
        destruct H5 as [ [A] | ].

        { assert ({A' | cuts_nTy A A'}) as [ A']
            by (apply cuts_nTy_dec).
          left.
          eexists.
          econstructor; eauto. }
        { right; intros; intro.
          inversion H5.
          assert (M' = nM2') by (eauto using cstu_nte_determinacy).
          rewrite <- H16 in  H13.
          assert (nctx' = G') by (eauto using cs_nctx_determinacy).
          rewrite H17 in H13.
          eapply n; eauto. }

        { right; intros; intro.
          inversion H2.
          assert (L = kindstar_nl_type).
          eauto using wftype_nl_determinacy.
          contradiction. }
        { right; intros; intro.
          inversion H2.
          eapply n; eauto. }
      * inversion H1.
    + intros.
      destruct M; inversion H1.
      assert ({A | wfterm_nl S G M1 A} + {forall A, ~ wfterm_nl S G M1 A})
        as [ [A] | ]
          by (eauto using IHsM1).
      * destruct A.

        { right; intros; intro.
          inversion H2.
          assert (typestar_nl_tcon tcon5 = typestar_nl_pi_intro nA2' nA1).
          eauto using wfterm_nl_determinacy.
          inversion H14. }
        { assert ({A1' | wfterm_nl S G M2 A1'} +
                  {forall A1', ~ wfterm_nl S G M2 A1'}) as [ [A1'] | ]
              by (eauto using IHsM2).

          assert ({walgeq_nl_Ty (erasure_nsgn S) (erasure_nctx G)
                                A1' A1 skind_nl_type} +
                  {~ (walgeq_nl_Ty (erasure_nsgn S) (erasure_nctx G)
                                   A1' A1 skind_nl_type)})
            as [ | ]
              by (eauto using walgeq_nTy_check,wfsig_nl_erasure).

          assert ({A1'' | tuts_nTy A1' M2 A1''})
            as [A1''] by (eauto using tuts_nTy_dec).
          
          left; eexists.
          econstructor; eauto.

          right; intros; intro.
          inversion H2.
          eapply n.
          assert (typestar_nl_pi_intro A1 A2
                  = typestar_nl_pi_intro nA2' nA1).
          eauto using wfterm_nl_determinacy.
          inversion H14.

          assert (A1' = nA2) by (eauto using wfterm_nl_determinacy).
          rewrite H15.
          auto.

          right; intros; intro.
          inversion H2.
          eapply n; eauto. }
        { right; intros; intro.
          inversion H2.
          assert (typestar_nl_pi_elim A nte5 =
                  typestar_nl_pi_intro nA2' nA1).
          eauto using wfterm_nl_determinacy.
          inversion H14. }
      * right; intros; intro.
        inversion H2.
        eapply n; eauto.      

Qed.

Lemma wftype_nl_dec (S : nsgn) (G : nctx) (A : nTy):
    wfsig_nl S -> wfctx_nl S G ->
    { L | wftype_nl S G A L } + { forall L, ~ (wftype_nl S G A L)}.
Proof.
  intros; eauto using wftype_nl_dec'.
Qed.

Lemma wfterm_nl_dec (S : nsgn) (G : nctx) (M : nte):
    wfsig_nl S -> wfctx_nl S G ->
    { A | wfterm_nl S G M A } + { forall A, ~ (wfterm_nl S G M A)}.
Proof.
  intros; eauto using wfterm_nl_dec'.
Qed.





