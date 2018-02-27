Require Import List.

Require Import defns.
Require Import sgn.

Definition ttgoal_true := ttgoal_unbound_at ttat_true.



Lemma goalterm_dec:
  forall (Sig : sgn) (G : ectx) (M : ete) (v : lnvar),
    { GA | r_goalterm Sig G M v (fst GA) (fst(snd GA)) (snd (snd GA)) }
    + {forall GA, ~ r_goalterm Sig G M (fst (fst GA)) (snd (fst GA)) (fst (snd GA)) (snd (snd GA))}
  with goaltype_dec:
  forall (Sig : sgn) (G : ectx) (A : eTy) (v : lnvar),
    { GA | r_goaltype Sig G A v (fst GA) (fst(snd GA)) (snd (snd GA)) }
    + {forall GA, ~ r_goaltype Sig G A (fst (fst GA)) (snd (fst GA)) (fst (snd GA)) (snd (snd GA))}.
Proof.
  {  intros Sig G M.
  induction M as [ c | i | A M | | v ].

  - (* con c in Sig *)

    intros.
    assert ({A | boundCon c A Sig} + {forall A, ~ boundCon c A Sig})
        as [ [A] | ]
           by (apply boundCon_dec).
    * left; exists (ttgoal_true, (A , v)); simpl.
      econstructor; eauto.
      admit.
    * right.
      intros; intro Hc.
      inversion Hc.
      eapply n; eauto.
  - (* ix *)
    generalize dependent G.
    induction i; intros.
    * destruct G as [ | A ].
      
      { right; intros; intro Hc.
        inversion Hc. }
      { left.
        exists (
            (ttgoal_unbound_at (ttat_shiftTy A 0 (typestar_nl_mtvar (S v))),
             (typestar_nl_mtvar (S v), S (S v)))); simpl.
        econstructor.
        simpl; auto. }
    * destruct G as [ | B ].

         { right; intros; intro Hc.
           inversion Hc. }
         { destruct IHi with G v as [ [ [ Go A' ] Hix ]  | ]; auto. }

  - intros.

    assert ({GA | r_goaltype Sig G A v (fst GA) (fst (snd GA)) (snd (snd GA))}
           + {forall GA , ~r_goaltype Sig G A (fst (fst GA)) (snd (fst GA)) (fst (snd GA)) (snd (snd GA))})
             by (apply goaltype_dec).

    destruct H as [ [ [ Go1 [ L v2 ] ]  ] | ].

    +  destruct IHM with v2 as [ [ [ Go2 [ B v3 ] ] ] |  ] ; simpl.

       * left.
         simpl in r.
         simpl in r0.
         
         exists ((ttgoal_conj (ttgoal_conj Go1 Go2)
                         (ttgoal_unbound_at (ttat_eq_K L kindstar_nl_type G))),
            (typestar_nl_pi_intro A B,
             v3)).
         simpl.
         econstructor; simpl; eauto.
       * right.
         intros. intro Hc.
         inversion Hc.          
         subst.
         apply n with ((lnvar2, Go2), (eB, snd (snd GA))).
         cbn.
         auto.

    + right.
      intros. intro Hc.
      destruct GA as [ [v1 Go1] [ B v2 ] ].
      simpl in Hc.
      generalize dependent n.
      inversion Hc.
      subst.
      intro.
      apply n with ((v1,Go0),(eL,lnvar2)).
      simpl.
      assumption.
  - (* pi elim *)

    intros.
    destruct IHM1 with v as [ [ [ Go1 [ A v1 ]] ] | Hn1 ].

    + simpl in r.

      destruct IHM2 with v1 as [ [ [ Go2 [ B v2 ]] ] | Hn2 ].

      * simpl in r0.
        left.
        exists (ttgoal_conj
                 (ttgoal_conj (ttgoal_conj Go1 Go2)
                              (ttgoal_unbound_at
                                 (ttat_eq_Ty A (typestar_nl_pi_intro B (typestar_nl_mtvar (S (S (S v2)))) ) G)))
                 (ttgoal_unbound_at
                    (ttat_substTy (typestar_nl_mtvar (S (S (S v2)))) M2 (typestar_nl_mtvar (S (S v2))))),
               (typestar_nl_mtvar (S (S v2)),
                 S ( S (S (S v2))))).

        simpl.
        apply r_g_te_pi_elim with v1 v2 (S (S v2)).
        eauto.
        eauto.
        simpl; auto.
        simpl; auto.

      * right.
        intros.
        intro Hc.
        generalize dependent Hn2.
        destruct GA as [ [ v2 Go2 ] [ B v3 ] ].
        simpl in Hc.
        inversion Hc.
        subst.

        intro Hn.
        apply Hn with ((lnvar2, Go3), (eA1, lnvar3)).
        simpl.
        auto.

    +  right.
       intros.
       intro Hc.
       generalize dependent Hn1.
       destruct GA as [ [ v2 Go2 ] [ B v3 ] ].
       simpl in Hc.
       inversion Hc.
       subst.
       
       intro Hn.
       apply Hn with ((v2, Go1), (eA, lnvar2)).
       simpl.
       auto.

  - intros.
    left.
    exists
      (ttgoal_bound_at v
                       (ttat_te (termstar_nl_mvar v) (typestar_nl_mtvar (S v0)) G),
       (typestar_nl_mtvar (S v0),
        S (S v0))).
    simpl.
    
    eapply r_g_te_mvar.
    simpl; auto.
  }
  

  {  intros Sig G A.
  induction A as [ a | A M | | v ].

  - (* tcon a in Sig *)

    intros.
    assert ({L | boundTCon a L Sig} + {forall L, ~ boundTCon a L Sig})
        as [ [L] | ]
           by (apply boundTCon_dec).
    * left; exists (ttgoal_true, (L , v)); simpl.
      econstructor; eauto.
      admit.
    * right.
      intros; intro Hc.
      inversion Hc.
      eapply n; eauto.
  - 
      
      
    (* end *)