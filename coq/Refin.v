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
  | typestar_nl_tcon a => mTy_leaf
  | typestar_nl_pi_intro A B => mTy_pi_intro (struct_eTy A) (struct_eTy B)
  | typestar_nl_pi_elim A M => mTy_pi_elim (struct_eTy A) (struct_ete M)
  | typestar_nl_mtvar _ => mTy_leaf
  end
with struct_ete (M : ete) : mte :=
  match M with
  | termstar_nl_con c => mte_leaf
  | termstar_nl_ix i => mte_leaf
  | termstar_nl_pi_intro A M => mte_pi_intro (struct_eTy A) (struct_ete M)
  | termstar_nl_pi_elim M N => mte_pi_elim (struct_ete M) (struct_ete N)
  | termstar_nl_mvar _ => mte_leaf
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
    generalize dependent v.
    generalize dependent M.
    (induction mM).
    (intros M v Heq).
    (destruct M as [c| i| A M| | mv]; inversion Heq).
  - (* con c in Sig *)

    (intros **).
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
           (ttgoal_unbound_at (ttat_shiftTy A 0 (typestar_nl_mtvar (S v))),
           (typestar_nl_mtvar (S v), S (S v))); simpl).
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
                     (ttat_shiftTy A1 0 (typestar_nl_mtvar (S v0)))),
               (typestar_nl_mtvar (S v0), S (S v0))).
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
                r_goalterm (map castSig Sig) G (termstar_nl_ix i)
                  (fst (fst (v0, Go0, (eA, lnvar2)))) Go0 eA lnvar2)).
             (apply n).
             (apply H).
             (simpl).
             auto. }         
  - (intros **).
    left.
    exists 
      (ttgoal_bound_at mv
         (ttat_te (termstar_nl_mvar mv) (typestar_nl_mtvar (S v)) G),
      (typestar_nl_mtvar (S v), S (S v))).
    (simpl).
    
    (eapply r_g_te_mvar).
    (simpl; auto).

  - (intros M v Heq).

    (destruct M as [| | A| | ]; inversion Heq).
    
    (assert
      ({GA : _ | r_goaltype (map castSig Sig) G A v (fst GA) (fst (snd GA)) (snd (snd GA))} +
       {(forall GA,
         ~
         r_goaltype (map castSig Sig) G A (fst (fst GA)) (snd (fst GA)) 
           (fst (snd GA)) (snd (snd GA)))}) by
      (apply goaltype_dec_str with sA; auto)).

    (destruct H as [[[Go1 [L v2]]]| ]).

    +  (destruct IHmM with M v2 as [[[Go2 [B v3]]]| ]; auto; simpl).

       * left.
         (simpl in r).
         (simpl in r0).
         
         exists 
           (ttgoal_conj (ttgoal_conj Go1 Go2)
              (ttgoal_unbound_at (ttat_eq_K L kindstar_nl_type G)),
           (typestar_nl_pi_intro A B, v3)).
         (simpl).
         (econstructor; simpl; eauto).
         
       * right.
         (intros **). intro Hc.
         (inversion Hc).          
         subst.
         (apply n with (lnvar2, Go2, (eB, snd (snd GA)))).
         (cbn).
         auto.

    + right.
      (intros **). intro Hc.
      (destruct GA as [[v1 Go1] [B v2]]).
      (simpl in Hc).
      generalize dependent n.
      (inversion Hc).
      subst.
      intro.
      (apply n with (v1, Go0, (eL, lnvar2))).
      (simpl).
      assumption.

    
  - (* pi elim *)
    (intros M v Heq).
    
    (destruct M; inversion Heq).
    (destruct IHmM1 with M1 v as [[[Go1 [A v1]]]| Hn1]; auto).
    
    + (simpl in r).

      (destruct IHmM2 with M2 v1 as [[[Go2 [B v2]]]| Hn2]; auto).

      * (simpl in r0).
        left.
        exists 
          (ttgoal_conj
             (ttgoal_conj (ttgoal_conj Go1 Go2)
                (ttgoal_unbound_at
                   (ttat_eq_Ty A
                      (typestar_nl_pi_intro B
                         (typestar_nl_mtvar (S (S (S v2))))) G)))
             (ttgoal_unbound_at
                (ttat_substTy (typestar_nl_mtvar (S (S (S v2)))) M2
                   (typestar_nl_mtvar (S (S v2))))),
          (typestar_nl_mtvar (S (S v2)), S (S (S (S v2))))).

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
        (apply Hn with (lnvar2, Go3, (eA1, lnvar3))).
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
       (apply Hn with (v2, Go1, (eA, lnvar2))).
       (simpl).
       auto.


    

  }
  

  {  (* intros Sig G A. *)
    generalize dependent v.
    generalize dependent A.
    (induction mA).

    (intros A v0 Heq).
    (destruct A as [a| A B| A IHA| v]; inversion Heq).

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
         (ttat_Ty (typestar_nl_mtvar v) (kindstar_nl_mkvar (S v0)) G),
      (kindstar_nl_mkvar (S v0), S (S v0))).
    (simpl).
    
    (eapply r_g_Ty_mvar).
    (simpl; auto).
      
  - (* pi intro *)
    (intros A v Heq).

    (destruct A; inversion Heq).
    
    (destruct IHmA1 with A1 v as [[[Go1 [L1 v2]]]| ]; simpl; auto).
    
    +  (destruct IHmA2 with A2 v2 as [[[Go2 [L2 v3]]]| ]; simpl; auto).

       * left.
         (simpl in r).
         (simpl in r0).
         
         exists 
           (ttgoal_conj
              (ttgoal_conj (ttgoal_conj Go1 Go2)
                 (ttgoal_unbound_at (ttat_eq_K L1 kindstar_nl_type G)))
              (ttgoal_unbound_at (ttat_eq_K L2 kindstar_nl_type G)),
           (kindstar_nl_type, v3)).
         (simpl).
         (econstructor; eauto).
       * right.
         (intros **). intro Hc.
         (inversion Hc).          
         subst.
         (apply n with (lnvar2, Go2, (eL2, snd (snd GA)))).
         (cbn).
         auto.

    + right.
      (intros **). intro Hc.
      (destruct GA as [[v1 Go1] [L v2]]).
      (simpl in Hc).
      generalize dependent n.
      (inversion Hc).
      subst.
      intro.
      (apply n with (v1, Go0, (eL1, lnvar2))).
      (simpl).
      assumption.
  - (* pi elim *)
    (intros A v Heq).

    (destruct A as [| | A M| ]; inversion Heq).

    (destruct IHmA with A v as [[[Go1 [L v1]]]| Hn1]; auto).

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
                   (ttat_eq_K (kindstar_nl_pi_intro B L)
                      (kindstar_nl_mkvar (S (S (S v2)))) G)))
             (ttgoal_unbound_at
                (ttat_substK (kindstar_nl_mkvar (S (S (S v2)))) M
                   (kindstar_nl_mkvar (S (S v2))))),
          (kindstar_nl_mkvar (S (S v2)), S (S (S (S v2))))).

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
        (apply Hn with (lnvar2, Go3, (eB, lnvar3)); simpl; auto).

    +  right.
       (intros **).
       intro Hc.
       generalize dependent Hn1.
       (destruct GA as [[v2 Go2] [B v3]]).
       (simpl in Hc).
       (inversion Hc).
       subst.
       
       intro Hn.
       (apply Hn with (v2, Go1, (eL, lnvar2)); simpl; auto).
}
Defined.

Lemma goalterm_dec :
  forall (Sig : sgn) (G : ectx) (M : ete) (v : lnvar),
  {GA : _ | r_goalterm (map castSig Sig) G M v (fst GA) (fst (snd GA)) (snd (snd GA))} +
  {(forall GA,
    ~
    r_goalterm (map castSig Sig) G M (fst (fst GA)) (snd (fst GA)) 
      (fst (snd GA)) (snd (snd GA)))} with goaltype_dec :
                                       forall (mA : mTy) 
                                         (Sig : sgn) 
                                         (G : ectx) 
                                         (A : eTy) 
                                         (v : lnvar),
                                       {GA : _ |
                                       r_goaltype (map castSig Sig) G A v 
                                         (fst GA) 
                                         (fst (snd GA)) 
                                         (snd (snd GA))} +
                                       {(forall GA,
                                         ~
                                         r_goaltype (map castSig Sig) G A 
                                           (fst (fst GA)) 
                                           (snd (fst GA)) 
                                           (fst (snd GA)) 
                                           (snd (snd GA)))}.
Proof.
  - (intros **).
    (apply goalterm_dec_str with (struct_ete M); auto).
  - (intros **).
    (apply goaltype_dec_str with (struct_eTy A); auto).
Defined.

     (*
Fixpoint progsig_dec (mM : mte) (Sig : sgn) (G : ectx) 
(M : ete) (v : lnvar) :
struct_ete M = mM ->
{GA : _ | g_sigprog (map castSig Sig) G M v (fst GA) (fst (snd GA)) (snd (snd GA))} +
{(forall GA,
  ~
  r_goalterm (map castSig Sig) G M (fst (fst GA)) (snd (fst GA)) 
  (fst (snd GA)) (snd (snd GA)))}
.
  *)
  
(* end *)