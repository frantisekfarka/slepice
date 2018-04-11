Require Import List.

Require Import Defns.
Require Import Sgn.

Definition ttgoal_true := ttgoal_unbound_at ttat_true.

Inductive mTy : Set :=
  | mTy_leaf : _
  | mTy_pi_intro : forall sA sB : mTy, _
  | mTy_pi_elim : forall (sA : mTy) (sM : mte), _
with mte : Set :=
  | mte_leaf : _
  | mte_pi_intro : forall (sA : mTy) (sM : mte), _
  | mte_pi_elim : forall sM sN : mte, _.

Fixpoint struct_eTy (A : eTy) : mTy :=
  match A with
  | ety_tcon a => mTy_leaf
  | ety_pi_intro A B => mTy_pi_intro (struct_eTy A) (struct_eTy B)
  | ety_pi_elim A M => mTy_pi_elim (struct_eTy A) (struct_ete M)
  | ety_mvar _ => mTy_leaf
  | ety_tvar _ => mTy_leaf
  end
with struct_ete (M : ete) : mte :=
  match M with
  | ete_con c => mte_leaf
  | ete_ix i => mte_leaf
  | ete_pi_intro A M => mte_pi_intro (struct_eTy A) (struct_ete M)
  | ete_pi_elim M N => mte_pi_elim (struct_ete M) (struct_ete N)
  | ete_mvar _ => mte_leaf
  | ete_tvar _ => mte_leaf
  end.
   


Fixpoint goalterm_dec_str (mM : mte) (Sig : sgn) (G : ectx) 
(M : ete) (v : lnvar) :
struct_ete M = mM ->
{GA : _ | r_goalterm (map castSig Sig) G M v (fst GA) (fst (snd GA)) (snd (snd GA))} +
{(forall GA,
  ~
  r_goalterm (map castSig Sig) G M (fst (fst GA)) (snd (fst GA)) 
    (fst (snd GA)) (snd (snd GA)))}
with goaltype_dec_str (mA : mTy) (Sig : sgn) (G : ectx) 
(A : eTy) (v : lnvar) :
struct_eTy A = mA ->
{GA : _ | r_goaltype (map castSig Sig) G A v (fst GA) (fst (snd GA)) (snd (snd GA))} +
{(forall GA,
  ~
  r_goaltype (map castSig Sig) G A (fst (fst GA)) (snd (fst GA)) 
    (fst (snd GA)) (snd (snd GA)))}.
Proof.
  {  (*intros Sig G M. *)
    generalize dependent G.
    generalize dependent v.
    generalize dependent M.
    (induction mM).
    (intros [c | i | A M | | mv | tv] v G Heq; inversion Heq).
    - (* con c in Sig *)
      
      (assert ({A : _ | boundCon c A (map castSig Sig)} + {(forall A, ~ boundCon c A (map castSig Sig))})
        as [[A]| ] by apply boundCon_dec).
      * (left; exists (ttgoal_true, (A, v)); simpl).
        (econstructor; eauto).
        eauto using boundCon_is_Ty_of_eTy.
      * right.
        (intros **; intro Hc).
        (inversion Hc).
        (eapply n; eauto).
    - (* ix *)
         generalize dependent G.
         generalize dependent Heq.
         (induction i; intros **).
          * (destruct G as [| A]).
      
            { (right; intros **; intro Hc).
              (inversion Hc). }
            { left.
              (exists 
                  (ttgoal_unbound_at (ttat_shiftTy A 0 (ety_tvar (S v))),
                   (ety_tvar (S v), S (S v))); simpl).
              simpl.
              econstructor.
              (simpl; auto). }
          * (destruct G as [| B]).
            
            { (right; intros **; intro Hc).
              (inversion Hc). }
            { (destruct IHi with G as [[[Go A'] Hix]| ]; auto).
              - left.
                (destruct A' as [A1 v0]).
                exists 
                  (ttgoal_conj Go
                               (ttgoal_unbound_at
                                  (ttat_shiftTy A1 0 (ety_tvar (S v0)))),
                   (ety_tvar (S v0), S (S v0))).
                (eapply r_g_te_var_cons).
                eauto.
                (simpl; auto).
              - right.
                (intros **).
                 (destruct GA as [[v0 Go] [A v1]]).
                 (simpl).
                 intro Hc.
                 (inversion Hc).
                 subst.
                 (assert
                    (~
                       r_goalterm (map castSig Sig) G (ete_ix i)
                       (fst (fst (v0, Go0, (eA, tvar2)))) Go0 eA tvar2)).
                 (apply n).
                 (apply H).
                 (simpl).
                 auto. }         
                 - (* mtvar *)
                     (intros **).
                      left.
                      exists 
                        (ttgoal_bound_at mv
                                         (ttat_te (ete_mvar mv) (ety_tvar (S v)) G),
                         (ety_tvar (S v), S (S v))).
                      (simpl).
                      
                      (eapply r_g_te_mvar).
                      (simpl; auto).

                      - intros.
                        left.
                        exists 
                        (ttgoal_unbound_at
                                         (ttat_te (ete_tvar tv) (ety_tvar (S v)) G),
                         (ety_tvar (S v), S (S v))).
                        (simpl).
                        constructor.
                        simpl; auto.
                        
                      - (* pi intro *)
                        (intros [ | | A M | | |  ] v G Heq ; inversion Heq).
    
                        (assert
                           ({GA : _ | r_goaltype (map castSig Sig) G A v (fst GA) (fst (snd GA)) (snd (snd GA))} +
                            {(forall GA,
                                 ~
                                   r_goaltype (map castSig Sig) G A (fst (fst GA)) (snd (fst GA)) 
                                   (fst (snd GA)) (snd (snd GA)))}) by
                            (apply goaltype_dec_str with sA; auto)).

    (destruct H as [[[Go1 [L v2]]]| ]).

    +  (destruct IHmM with M v2 (A :: G) as [[[Go2 [B v3]]]| ]; auto; simpl).

       * left.
         (simpl in r).
         (simpl in r0).
         
         exists 
           (ttgoal_conj (ttgoal_conj Go1 Go2)
              (ttgoal_unbound_at (ttat_eq_K L ek_type G)),
           (ety_pi_intro A B, v3)).
         (simpl).
         (econstructor; simpl; eauto).
         
       * right.
         (intros **). intro Hc.
         (inversion Hc).          
         subst.
         (apply n with (tvar2, Go2, (eB, snd (snd GA)))).
         simpl.
         auto.

    + right.
      (intros **). intro Hc.
      (destruct GA as [[v1 Go1] [B v2]]).
      (simpl in Hc).
      generalize dependent n.
      (inversion Hc).
      subst.
      intro.
      (apply n with (v1, Go0, (eL, tvar2))).
      (simpl).
      assumption.

    
  - (* pi elim *)
    (intros [ | | | M1 M2 | | ] v G Heq; inversion Heq).
    
    (destruct IHmM1 with M1 v G as [[[Go1 [A v1]]]| Hn1]; auto).
    
    + (simpl in r).

      (destruct IHmM2 with M2 v1 G as [[[Go2 [B v2]]]| Hn2]; auto).

      * (simpl in r0).
        left.
        exists 
          (ttgoal_conj
             (ttgoal_conj (ttgoal_conj Go1 Go2)
                (ttgoal_unbound_at
                   (ttat_eq_Ty A
                      (ety_pi_intro B
                         (ety_tvar (S (S (S v2))))) (ek_type) G)))
             (ttgoal_unbound_at
                (ttat_substTy (ety_tvar (S (S (S v2)))) M2
                   (ety_tvar (S (S v2))))),
          (ety_tvar (S (S v2)), S (S (S (S v2))))).

        (simpl).
        (apply r_g_te_pi_elim with v1 v2 (S (S v2))).
        eauto.
        eauto.
        (simpl; auto).
        (simpl; auto).

      * right.
        (intros **).
        intro Hc.
        generalize dependent Hn2.
        (destruct GA as [[v2 Go2] [B v3]]).
        (simpl in Hc).
        (inversion Hc).
        subst.

        intro Hn.
        (apply Hn with (tvar2, Go3, (eA1, tvar3))).
        (simpl).
        auto.

    +  right.
       (intros **).
       intro Hc.
       generalize dependent Hn1.
       (destruct GA as [[v2 Go2] [B v3]]).
       (simpl in Hc).
       (inversion Hc).
       subst.
       
       intro Hn.
       (apply Hn with (v2, Go1, (eA, tvar2))).
       (simpl).
       auto.


    

  }
  

  {  (* intros Sig G A. *)
    generalize dependent G.     
    generalize dependent v.
    generalize dependent A.
    (induction mA).

    (intros [a| A B| A IHA| v | t ] v0 G Heq ; inversion Heq).

  - (* tcon a in Sig *)

    (intros **).
    (assert ({L : _ | boundTCon a L (map castSig Sig)} + {(forall L, ~ boundTCon a L (map castSig Sig))})
      as [[L]| ] by apply boundTCon_dec).
    * (left; exists (ttgoal_true, (L, v0)); simpl).
      (econstructor; eauto).
      eauto using boundTCon_is_K_of_eK.
    * right.
      (intros **; intro Hc).
      (inversion Hc).
      (eapply n; eauto).

  - (intros **).
    left.
    exists 
      (ttgoal_unbound_at
         (ttat_Ty (ety_mvar v) (ek_tvar (S v0)) G),
      (ek_tvar (S v0), S (S v0))).
    (simpl).
    
    (eapply r_g_Ty_mvar).
    (simpl; auto).

     - intros **.
       left.
       exists (ttgoal_unbound_at
            (ttat_Ty (ety_tvar t) (ek_tvar (S v0)) G),
             (ek_tvar (S v0), S (S v0))).
       simpl; constructor.
       simpl; auto.
       
  - (* pi intro *)
    (intros [ | A1 A2 | | | ] v G Heq; inversion Heq).
    
    (destruct IHmA1 with A1 v G as [[[Go1 [L1 v2]]]| ]; simpl; auto).
    
    +  (destruct IHmA2 with A2 v2 (A1 :: G) as [[[Go2 [L2 v3]]]| ]; simpl; auto).

       * left.
         (simpl in r).
         (simpl in r0).
         
         exists 
           (ttgoal_conj
              (ttgoal_conj (ttgoal_conj Go1 Go2)
                 (ttgoal_unbound_at (ttat_eq_K L1 ek_type G)))
              (ttgoal_unbound_at (ttat_eq_K L2 ek_type G)),
           (ek_type, v3)).
         (simpl).
         (econstructor; eauto).
       * right.
         (intros **). intro Hc.
         (inversion Hc).          
         subst.
         (apply n with (tvar2, Go2, (eL2, snd (snd GA)))).
         (simpl).
         auto.

    + right.
      (intros **). intro Hc.
      (destruct GA as [[v1 Go1] [L v2]]).
      (simpl in Hc).
      generalize dependent n.
      (inversion Hc).
      subst.
      intro.
      (apply n with (v1, Go0, (eL1, tvar2))).
      (simpl).
      assumption.
  - (* pi elim *)
    (intros [| | A M| | ] v G Heq; inversion Heq).

    (destruct IHmA with A v G  as [[[Go1 [L v1]]]| Hn1]; auto).

    + (simpl in r).

      (assert
        (IHM :
         {GA : _ |
         r_goalterm (map castSig Sig) G M v1 (fst GA) (fst (snd GA)) (snd (snd GA))} +
         {(forall GA,
           ~
           r_goalterm (map castSig Sig) G M (fst (fst GA)) (snd (fst GA)) 
             (fst (snd GA)) (snd (snd GA)))}) by
        (apply goalterm_dec_str with sM; auto)).

      
      (destruct IHM as [[[Go2 [B v2]]]| Hn2]).
      
      * (simpl in r0).
        left.
        
        exists 
          (ttgoal_conj
             (ttgoal_conj (ttgoal_conj Go1 Go2)
                (ttgoal_unbound_at
                   (ttat_eq_K (ek_pi_intro B L)
                      (ek_tvar (S (S (S v2)))) G)))
             (ttgoal_unbound_at
                (ttat_substK (ek_tvar (S (S (S v2)))) M
                   (ek_tvar (S (S v2))))),
          (ek_tvar (S (S v2)), S (S (S (S v2))))).

        (simpl).
        (apply r_g_Ty_pi_elim with v1 v2 (S (S v2)); simpl; auto).

      * right.
        (intros **).
        intro Hc.
        generalize dependent Hn2.
        (destruct GA as [[v2 Go2] [B v3]]).
        (simpl in Hc).
        (inversion Hc).
        subst.

        intro Hn.
        (apply Hn with (tvar2, Go3, (eB, tvar3)); simpl; auto).

    +  right.
       (intros **).
       intro Hc.
       generalize dependent Hn1.
       (destruct GA as [[v2 Go2] [B v3]]).
       (simpl in Hc).
       (inversion Hc).
       subst.
       
       intro Hn.
       (apply Hn with (v2, Go1, (eL, tvar2)); simpl; auto).
}
Defined.

Lemma goalterm_dec :
  forall (Sig : sgn)
    (G : ectx)
    (M : ete)
    (v : tvar),
    {GoA : _ |
     r_goalterm (map castSig Sig) G M v
                (fst GoA)
                (fst (snd GoA))
                (snd (snd GoA))} +
    {(forall GoA : (tvar * TTGoal * (eTy * tvar)) ,
         ~
           r_goalterm (map castSig Sig) G M
           (fst (fst GoA))
           (snd (fst GoA)) 
           (fst (snd GoA))
           (snd (snd GoA)))}
with goaltype_dec :
       forall (Sig : sgn) 
         (G : ectx) 
         (A : eTy) 
         (v : lnvar),
         {GoL : _ |
          r_goaltype (map castSig Sig) G A v 
                     (fst GoL) 
                     (fst (snd GoL)) 
                     (snd (snd GoL))} +
         {(forall GoL,
              ~
                r_goaltype (map castSig Sig) G A 
                (fst (fst GoL)) 
                (snd (fst GoL)) 
                (fst (snd GoL)) 
                (snd (snd GoL)))}.
Proof.
  - (intros **).
    (apply goalterm_dec_str with (struct_ete M); auto).
  - (intros **).
    (apply goaltype_dec_str with (struct_eTy A); auto).
Defined.

Fixpoint pesig_dec (v : tvar) :
  {Pv : _ | r_pe v (fst Pv) (snd Pv)}.
Proof.
  exists (ttprog_hc_nob ttprog_empty
     (ttpt_axType)
     (ttat_eq_K ek_type ek_type nil), v).
  simpl.
  constructor.
Qed.
     
Fixpoint progsig_dec (Sig : sgn) (v : tvar) :
{Pv : _ | r_prog (map castSig Sig) v (fst Pv) (snd Pv)} +
{(forall Pv,
  ~
  r_prog (map castSig Sig) (fst Pv) (fst (snd Pv)) 
  (snd (snd Pv)))}
.
Proof.
  induction Sig as [ | [ [c [A wA ]]  | [a [L wL]] ] ]; simpl.
  - 
    left.

    assert {PeV | r_pe v (fst PeV) (snd PeV)} as [ [Pempty v'] Hrpe ]
      by (apply pesig_dec; assumption).
    
    exists (Pempty, v').
    constructor.
    assumption.
    
  - destruct IHSig as [ [[P v''] wP ] | Hn ].

    + left.
      exists (ttprog_hc_nob (ttprog_hc_nob (ttprog_hc_nob (ttprog_hc_nob P
              (ttpt_axCon c)  (ttat_te (ete_con c) A nil))
              (ttpt_axShiftC) (ttat_shiftte (ete_con c) 0 (ete_con c)))
              (ttpt_axSubstC) (ttat_substte (ete_con c) (ete_tvar ( S v'')) (ete_con c)))
              (ttpt_axEqCon)  (ttat_eq_te (ete_con c) (ete_con c) A nil)         
           , S v'').
        
        apply r_p_sgn_con with v''.

        assumption.
        simpl in wP.
        assumption.

        simpl; auto.

    + right.
      intro Pv.
      destruct Pv as [ v' [ P v'']].
      intro Hc.
      inversion Hc.
      
      
      apply Hn with (v', (TTP, tvar2)).

      simpl.
      simpl in H6.
      subst.
      auto.

  - destruct IHSig as [ [[P v''] wP ] | Hn ].

    + left.
      exists (ttprog_hc_nob (ttprog_hc_nob (ttprog_hc_nob (ttprog_hc_nob P
              (ttpt_axTCon a) (ttat_Ty (ety_tcon a) L nil))
              (ttpt_axShiftC) (ttat_shiftTy (ety_tcon a) 0 (ety_tcon a)))
              (ttpt_axSubstC) (ttat_substTy (ety_tcon a) (ete_tvar ( S v'')) (ety_tcon a)))
              (ttpt_axEqTCon)   (ttat_eq_Ty (ety_tcon a) (ety_tcon a) L nil)                        
           , S v'').

        
        apply r_p_sgn_tcon with v''.

        assumption.
        simpl in wP.
        assumption.

        simpl; auto.

    + right.
      intro Pv.
      destruct Pv as [ v' [ P v'']].
      intro Hc.
      inversion Hc.
      
      
      apply Hn with (v', (TTP, tvar2)).

      simpl.
      simpl in H6.
      subst.
      auto.
Qed.

        
(* end *)