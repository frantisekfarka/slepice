Require Import List.
        


Require Import defns.

Require Import nl_sgn.
Require Import nl_eq.
Require Import nl_fusion.
Require Import nl_struct.


(** algeq mockup **)
Lemma algeq_nTy_check:
  forall (sS : snsgn) (sG : snctx) (M N : nte) (tau : snTy),
    wfssig_nl sS ->
    { algeq_nl_te sS sG M N tau } +
    { ~ algeq_nl_te sS sG M N tau}.
Admitted.

(** * weak algorithmic equality **)

(** determinacy **)

Lemma walgeq_nTy_determinacy':
  forall (sA : sTy) (sS : snsgn) (sG : snctx) (A1 A2 : nTy)
    (kappa1 kappa2 : snK),
    sA = struct_nTy A1 ->
    wfssig_nl sS ->
    walgeq_nl_Ty sS sG A1 A2 kappa1 ->
    walgeq_nl_Ty sS sG A1 A2 kappa2 ->
    kappa1 = kappa2.
Proof.
  intros.
  generalize dependent kappa2.
  generalize dependent kappa1.
  generalize dependent A2.
  generalize dependent A1.
  generalize dependent sG.
               
  induction sA; intros sG A1 Hstruct A2 kappa1 Hwalg1 kappa2 Hwalg2;
  destruct A1 as [a | A11 A12 | A1 M1 ];
  destruct A2 as [a' | A21 A22 | A2 M2 ];
  inversion Hstruct;
  try (solve [inversion Hwalg1 ]).

  - (* tcon case *)
    inversion Hwalg1.
    inversion Hwalg2.
    subst.
    eauto using boundsnTCon_determinacy.

  - inversion Hwalg2.
    inversion Hwalg1.
    reflexivity.

  - (* pi_elim case *)
    inversion Hwalg1.
    inversion Hwalg2.

    assert (Heq : skind_nl_pi_intro tau kappa1
            = skind_nl_pi_intro tau0 kappa2).
    eapply IHsA; eauto.

    inversion Heq.
    reflexivity.
Qed.

Lemma walgeq_nTy_determinacy:
  forall (sS : snsgn) (sG : snctx) (A1 A2 : nTy)
    (kappa1 kappa2 : snK),
    wfssig_nl sS ->
    walgeq_nl_Ty sS sG A1 A2 kappa1 ->
    walgeq_nl_Ty sS sG A1 A2 kappa2 ->
    kappa1 = kappa2.
Proof.
  intros; eauto using walgeq_nTy_determinacy'.
Qed.  

(** decidability **)

Lemma walgeq_nTy_dec':
  forall (sA : sTy) (sS : snsgn) (sG : snctx) (A1 A2 : nTy),
    sA = struct_nTy A1 -> 
    wfssig_nl sS ->
    { kappa | walgeq_nl_Ty sS sG A1 A2 kappa } +
    { forall kappa , ~ (walgeq_nl_Ty sS sG A1 A2 kappa) }.
Proof.
  intro sA.
  induction sA; intros sS sG A1 A2 Hstruct HwfsS.
  
  - destruct A1 as [a | | ] ; try (inversion Hstruct).
    destruct A2 as [a' | | ];
      try (solve [right ; intros; intro Hc; inversion Hc]).

    assert ({a = a'} + {a <> a'})
        as [ e | ]
          by (apply eq_tcon).
    + subst.
      assert ({kappa | boundsnTCon a' kappa sS} +
              {forall kappa, ~ boundsnTCon a' kappa sS})
        as [ [kappa] | ]
          by (eauto using boundsnTCon_dec).
        * left; eexists; econstructor; eauto.
        * right; intros; intro Hwalg; inversion Hwalg.
          eapply n; eauto.
    + right; intros; intro Hwalg; inversion Hwalg.
      contradiction.
  - destruct A1 as [ | A11 A12 | ];
    destruct A2 as [ | A21 A22 | ];
    inversion Hstruct;
    try (solve [right; intros; intro Hc; inversion Hc ]).

    + assert ({kappa | walgeq_nl_Ty sS sG A11 A21 kappa} +
              {forall kappa, ~ walgeq_nl_Ty sS sG A11 A21 kappa})
        as [[kappa'] | ]
          by (apply IHsA1; auto).
      
      * assert ({kappa' = skind_nl_type} + {kappa' <> skind_nl_type})
          as [ | ]
            by (apply eq_snK).

        { (*  *)
          assert ({ A12' | cstu_nTy A12 0 A12'})
            as [ A12' ]
              by (eapply cstu_nTy_dec).
          assert ({ A22' | cstu_nTy A22 0 A22'})
            as [ A22' ]
              by (eapply cstu_nTy_dec).

          assert ({kappa'' | walgeq_nl_Ty sS (erasure_nTy A11 :: sG)
                                A12' A22' kappa''} +
                  {forall kappa'', ~(walgeq_nl_Ty sS (erasure_nTy A11 :: sG)
                                  A12' A22' kappa'')})
            as [ [kappa''] | ]
              by (apply IHsA2; subst; eauto using struct_nTy_cstu).

          - assert ({kappa'' = skind_nl_type} + {kappa'' <> skind_nl_type})
              as [ | ]
                by (apply eq_snK).

            subst.
            left ; eexists; econstructor; eauto.

            right; intros; intro Heq.
            inversion Heq.
            assert (Heq1 : A12' = nA2')
              by (eauto using cstu_nTy_determinacy).

            assert (Heq2 : A22' = nB2')
              by (eauto using cstu_nTy_determinacy).            
            subst.
            apply n.
            eapply walgeq_nTy_determinacy; eauto.

          - right; intros; intro Hc; inversion Hc.
            
            assert (Heq1 : A12' = nA2')
              by (eauto using cstu_nTy_determinacy).

            assert (Heq2 : A22' = nB2')
              by (eauto using cstu_nTy_determinacy).

            subst.
            eapply n; eauto. }

        { right; intros; intro Hc; inversion Hc.
          apply n.

          eapply walgeq_nTy_determinacy; eauto. }         

      * right; intros; intro Hc; inversion Hc.
        eapply n; eauto.

  - destruct A1 as [ | | A1 M1 ] ; 
    destruct A2 as [ | | A2 M2];
    inversion Hstruct;
    try (solve [ right ; intros; intro Hc; inversion Hc ]).

    assert ({kappa' | walgeq_nl_Ty sS sG A1 A2 kappa'} +
            {forall kappa', ~ walgeq_nl_Ty sS sG A1 A2 kappa'})
      as [ [ [ | tau kappa'] ]  | ]
           by (apply IHsA; auto).

    + right; intros; intro Hc; inversion Hc.

      assert (Hcontra : skind_nl_type = skind_nl_pi_intro tau kappa)
        by (eapply walgeq_nTy_determinacy; eauto).

      inversion Hcontra.

    + assert ({algeq_nl_te sS sG M1 M2 tau} +
              {~ algeq_nl_te sS sG M1 M2 tau})
        as [ | ]
          by (apply algeq_nTy_check; eauto).

      * left; eexists; econstructor; eauto.
      * right; intros; intro Hc; inversion Hc.

        assert (Heq : skind_nl_pi_intro tau kappa'
                      = skind_nl_pi_intro tau0 kappa)
          by (eapply walgeq_nTy_determinacy; eauto).
        inversion Heq.
        subst.
        contradiction.

    + right; intros; intro Hc; inversion Hc.
      eapply n; eauto.
Qed.

Lemma walgeq_nTy_dec:
  forall (sS : snsgn) (sG : snctx) (A1 A2 : nTy),
    wfssig_nl sS ->
    { kappa | walgeq_nl_Ty sS sG A1 A2 kappa } +
    { forall kappa , ~ (walgeq_nl_Ty sS sG A1 A2 kappa) }.
Proof.
  intros; eauto using walgeq_nTy_dec'.
Qed.


(** wagleq checking **)

Lemma walgeq_nTy_check:
  forall (sS : snsgn) (sG : snctx) (A1 A2 : nTy) (kappa : snK),
    wfssig_nl sS ->
    { walgeq_nl_Ty sS sG A1 A2 kappa} +
    { ~ (walgeq_nl_Ty sS sG A1 A2 kappa) }.
Proof.
  intros.

  assert ({kappa' | walgeq_nl_Ty sS sG A1 A2 kappa'} +
          {forall kappa', ~ walgeq_nl_Ty sS sG A1 A2 kappa'})
    as [ [kappa'] | ]
      by (eauto using walgeq_nTy_dec).

  - assert ({kappa = kappa'} + {kappa <> kappa'})
      as [ | ]
        by (apply eq_snK).

    + subst; left; auto.
    + right; intro.
      assert (kappa = kappa') by (eauto using walgeq_nTy_determinacy).
      contradiction.
  - right; intro.
    eapply n; eauto.
Qed.




