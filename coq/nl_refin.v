Require Import List.


Require Import defns.
Require Import nl_sgn.

Definition ttgoal_true := ttgoal_unbound_at ttat_true.
Definition ttgoal_cuTy A i A' := ttgoal_unbound_at (ttat_cuTy A i A').


Lemma goalterm_nl_dec:
  forall {sM : ste}  (Sig : nsgn) (G : nctx) (M : nte),
    sM = struct_nte M ->
    { GA | goalterm_nl Sig G M (fst GA) (snd GA) }
    + {forall GA, ~ goalterm_nl Sig G M (fst GA) (snd GA)}.
Proof.
  intros sM Sig.
  induction sM.

  - (* leaf *)

    intros.
    destruct M as [ c | | | | | mx ]; inversion H.
    
    + (* con *)
      assert ({A | boundnCon c A Sig} + {forall A, ~ boundnCon c A Sig})
        as [ [A] | ]
          by (apply boundnCon_dec).
      * left; exists (ttgoal_true, A); cbn.
        constructor; auto.
      * right.
        intros; intro Hc.
        inversion Hc.
        eapply n; eauto.
    +  generalize dependent G.
       induction ixc; intros.
       * destruct G as [ | A ].

         { right; intros; intro Hc.
           inversion Hc. }
         { left.
           exists (ttgoal_true, A).
           constructor. }
       * destruct G as [ | B ].

         { right; intros; intro Hc.
           inversion Hc. }
         {
           (* from decidability ??? *)
           assert ({ G'B' | cu_nctx (B :: G) 0 (fst G'B') (snd G'B')})
             as [ [ G' B' ]  HcuTy  ]
               by (admit).
           
           cbn in HcuTy.

           destruct IHixc with G' as [ [ [ Go A' ] Hixc ]  | ]; auto.
           
           - cbn in Hixc.

             left.
             (* fresh name ? *)
             assert (mA : mtvar) by (admit).
             exists (ttgoal_conj  Go (ttgoal_cuTy A' 0 (typestar_nl_mtvar mA)),
                typestar_nl_mtvar mA).
             cbn.
             econstructor; eauto.

           - right.
             intros. intro Hc.
             inversion Hc.          
             apply n with (G0, nA').
             subst.
             cbn.
             (* from determianacy : *)
             assert (G' = nG') by (admit).
             assert (B' = nB') by (admit).
             subst.
             auto. }
    + right; intros; intro Hc.
      inversion Hc.

    + (* mvar *)
      left.
      (* fresh mvar *)
      assert (mA : mtvar) by (admit).
      
      exists (ttgoal_bound_at mx (ttat_Ty (typestar_nl_mtvar mA) G), (typestar_nl_mtvar mA)).
      constructor.

  - intros G M HsM.
    destruct M as [ | | | A M |  | ]; inversion HsM.
  
    assert ({ G' | cs_nctx G 0 A G'})
      as [ G' HG' ]
           by (admit).

    assert ({M' | cstu_nte M 0 M'})
      as [ M' HM' ]
           by (admit).

    destruct IHsM with G' M' as [ [ [Go B] HGo ] | ].

    (* cstu_nte preservers struct *)
    admit.

    + (* fresh *)
      assert (mB' : mtvar) by (admit).
    
      left.
      exists (ttgoal_conj Go (ttgoal_unbound_at (ttat_cutsTy B (typestar_nl_mtvar mB'))),
         typestar_nl_pi_intro A (typestar_nl_mtvar mB')).

      econstructor; eauto.

    + right.
      intros. intro Hc.
      inversion Hc.

      (* from determianacy *)
      assert (G' = nG') by (admit).
      assert (M' = nM') by (admit).

      apply n with (GA := (G0, nB)).
        
      subst. auto.

  - intros G M HsM.
    destruct M; inversion HsM.

    destruct IHsM1 with G M1 as [ [ [Go1 A1] HGo1 ] | ].
    auto.

    + 
      destruct IHsM2 with G M2 as [ [ [Go2 A2] HGo2 ] | ].
      auto.

      * 
        assert (B : mtvar) by (admit).
        assert (B' : mtvar) by (admit).   
    
        left.
    
        exists (ttgoal_conj
             (ttgoal_conj
                (ttgoal_conj
                   Go1
                   Go2)
                (ttgoal_unbound_at
                   (ttat_eq_Ty
                      A1
                      (typestar_nl_pi_intro A2 (typestar_nl_mtvar B))
                      G )))
             (ttgoal_unbound_at
                (ttat_tutsTy (typestar_nl_mtvar B) M2 (typestar_nl_mtvar B'))),
           typestar_nl_mtvar B').
        
        constructor; auto.

      * (* not goalterm M2 *)

        right.
        intros. intro Hc.

        inversion Hc.
        eapply n with (G2, nA2); auto.

    +  (* not goalterm M1 *)
      
      right.
      intros. intro Hc.

      inversion Hc.
      eapply n with (G1, nA1); auto.

Admitted.



      
      
    (* end *)