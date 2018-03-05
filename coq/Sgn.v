Require Import List.
Require Import Defns.

Require Import Eq.


(**
  * boundCon is Ty
 **)
Lemma boundCon_is_Ty_of_eTy :
  forall (S : sgn) (c : con) (A : eTy), boundCon c A S -> is_Ty_of_eTy A.
Proof.
  (intros **).
  (induction S).
  - (unfold boundCon in H).
    decompose record H.
    (simpl in H0).
    (apply app_cons_not_nil in H0).
    contradiction.

  - (destruct a as [[c0 [A' wA']]| ]).

    + (assert ({c = c0} + {c <> c0}) as [| ] by apply eq_con).

      * subst.

        (assert ({A = A'} + {A <> A'}) as [| ] by apply eq_eTy_dec).                                

        { subst.
          assumption. }
        { (apply IHS).
          (unfold boundCon in H).
          decompose record H.
          (unfold boundCon).
          (simpl in H0).
          (destruct x).
          - (simpl in H0).
            (inversion H0).
            (symmetry in H3; contradiction).
          - exists x.
              exists x0.

              split.
              (inversion H0; auto).
              intro.
              (apply H2).
              (right; auto). }
      * (apply IHS).
        (unfold boundCon in H).
        decompose record H.
        (unfold boundCon).
        (simpl in H0).
        (destruct x).
        { (simpl in H0).
          (inversion H0).
          (symmetry in H3; contradiction). }
        { exists x.
          exists x0.

          split.
          (inversion H0; auto).
          intro.
          (apply H2).
          (right; auto). }
          
    + (destruct p as [a [L wL]]).
      (apply IHS).
      (unfold boundCon in H).
      decompose record H.
      (unfold boundCon).
      (destruct x).
      * (inversion H0).
      * exists x.
          exists x0.

          split.
          (inversion H0; auto).
          intro.
          (apply H2).
          (right; auto).
Qed.

(**
  * boundTCon is K
 **)
Lemma boundTCon_is_K_of_eK :
  forall (S : sgn) (a : tcon) (L : eK), boundTCon a L S -> is_K_of_eK L.
Proof.
  (intros **).
  (induction S as [| el]).
  - (unfold boundTCon in H; decompose record H).
    (apply app_cons_not_nil in H0).
    contradiction.

  - (destruct el as [[c [A]]| [a0 [L' wL']]]).

    + (apply IHS).
      (unfold boundTCon in H).
      decompose record H.
      (unfold boundTCon).
      (destruct x).
      * (inversion H0).
      * exists x.
          exists x0.

          split.
          (inversion H0; auto).
          intro.
          (apply H2).
          (right; auto).
    
    + (assert ({a0 = a} + {a0 <> a}) as [| ] by apply eq_con).

      * subst.

        (assert ({L' = L} + {L' <> L}) as [| ] by apply eq_eK).                                

        { subst.
          assumption. }
        { (apply IHS).
          (unfold boundTCon in H).
          decompose record H.
          (unfold boundTCon).
          (destruct x).
          - (inversion H0).
            contradiction.
          - exists x.
              exists x0.

              split.
              (inversion H0; auto).
              intro.
              (apply H2).
              (right; auto). }
      * (apply IHS).
        (unfold boundTCon in H).
        decompose record H.
        (simpl in H0).
        (destruct x).
        { (inversion H0).
          contradiction. }
        { exists x.
          exists x0.

          split.
          (inversion H0; auto).
          intro.
          (apply H2).
          (right; auto). }          

Qed.

          


(**
  * boundCon
 **)

(** decidability of boundCon **)

Lemma boundCon_dec :
  forall (S : sgn) (c : con),
  {A : _ | boundCon c A S} + {(forall A, ~ boundCon c A S)}.
Proof.
  (induction S; intros **).

  - right.
    (intros **). intro Hc.
    (unfold boundCon in Hc).
    decompose record Hc.
    (apply app_cons_not_nil in H).
    contradiction.

  - (destruct a).

    + (destruct p).

      (assert ({c = c0} + {c <> c0}) as [| ] by apply eq_con; subst).

      * (destruct s).
        left.
        exists x.
        exists nil.
        eexists.
        (simpl).
        split.
        auto.
        intro.
        auto.
      * (destruct IHS with c).
        (destruct s0).       

        { left.
          exists x.
          (unfold boundCon).
          (simpl).
          (unfold boundCon in b).
          decompose record b.
          exists (inl (c0, proj1_sig s) :: x0). 
          exists x1.
          (simpl).
          split.
          (rewrite H).
          auto.
          intro.
          (inversion H0).
          (inversion H2).
          (apply n; auto).
          (apply H1; auto).
        }
        {
          right.
          (intros **).
          intro.  
          (unfold boundCon in H).
          decompose record H.
          (destruct x).
          - (inversion H0).
            (apply n).
            auto.
            
          - (assert (map castSig S = x ++ inl (c, A) :: x0)).
            (inversion H0).
            auto.
            (apply n0 with A).
            (unfold boundCon).
            (rewrite H1).
            exists x.
            exists x0.
            split.
            auto.
            intro.
            (apply H2). 
            right.
            assumption.
        }
    +  (* inr cases *)
      (destruct IHS with c).

      * (* bound cases *)
        left.
        (destruct s).
        (destruct p).
        exists x.
        (unfold boundCon in b).
        decompose record b.
        (unfold boundCon).
        (simpl).
        (rewrite H).
        exists (inr (t, proj1_sig s) :: x0).
        exists x1.
        (simpl).
        split.
        
        auto.
        (intros **).
        intro.
        (apply H1).
        (inversion H0).
        (inversion H2).
        assumption.
      * (* not bound at all *)
        right.
        (intros **).
        intro.
        (destruct p).
        (apply n with A).
        (unfold boundCon in H).
        decompose record H.
        (destruct x).
        (inversion H0).
        (inversion H0).
        exists x.
        exists x0.
        split.
        auto.
        (intros **).
        intro.
        (apply H2).
        right.
      assumption.
Defined.  

(** determianacy of boundnCon **)

Lemma boundnCon_weak_r :
  forall (Sig : sgn) (c : con) (a : tcon) (A : eTy)
    (L : {eK : _ | is_K_of_eK eK}),
  boundCon c A (inr (a, L) :: Sig) -> boundCon c A Sig.
Proof.
  (intros **).
  (unfold boundCon in H).
  decompose record H.
  (destruct x).
  - (inversion H0).
  -
    exists x.    
      exists x0.
      (inversion H0).
      split.
      auto.
      (intros **).
      intro.
      (apply H2).
      right.
      assumption.
Qed.  

Lemma boundnCon_weak_l :
  forall (S : sgn) (c d : con) (A : eTy) (B : {eTy : _ | is_Ty_of_eTy eTy}),
  boundCon c A (inl (d, B) :: S) -> c <> d -> boundCon c A S.
Proof.
  (intros **).
  (unfold boundCon in H).
  decompose record H.
  (destruct x).
  (inversion H1).
  (destruct H0).
  (symmetry; assumption).
  exists x.
  exists x0.
  (inversion H1).
  split.
  auto.
  (intros **).
  intro.
  (apply H3).
  right.
  assumption.
Qed.  

(*
Lemma boundnCon_weak_determinacy:
  forall (S : sgn) (c : con) (A1 A2 : eTy),
    boundnCon c A1 (inl (c, A2) :: S) ->
    ~ indomnCon c S
    -> A1 = A2.
Proof.
  intros.
  unfold boundnCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  reflexivity.
  destruct H0.
  exists A1.
  exists x.
  exists x0.
  split.
  inversion H1.
  reflexivity.
  intros; intro.
  apply H3 with nA'.
  right.
  assumption.
Qed.
 *)

(*
Lemma boundCon_determinacy:
  forall (S : sgn) (c : con) (A1 A2 : eTy),
    wfsig_nl S ->
    boundCon c A1 S ->
    boundCon c A2 S ->
    A1 = A2.
Proof.
  intros.
  induction H.
  (* nil case *)
  intros.
  unfold boundnCon in H0.
  decompose record H0.
  apply app_cons_not_nil in H.
  contradiction.
  (* step case *)
  intros.
  apply IHwfsig_nl; eapply boundnCon_weak_r ; eauto.
  (* *)
  assert ({c = c0} + {c <> c0}) by (apply eq_con).
  destruct H4.
  rewrite e in H0.
  rewrite e in H1.
  assert (A1 = nA).
  eauto using boundnCon_weak_determinacy; auto.
  assert (A2 = nA).
  eauto using boundnCon_weak_determinacy; auto.
  rewrite H4.
  rewrite H5.
  reflexivity.
  apply IHwfsig_nl; eauto using boundnCon_weak_l; auto.
Qed.
*)

(**
  * boundsnCon
 **)

(* 

(** decidability of boundsnCon **)

Lemma boundsCon_dec:
  forall (sS :ssgn) (c : con),
    { tau | boundsCon c tau sS } +
    { forall tau, ~boundsCon c tau sS }.
Proof.
  intros.
  induction sS.
  right.
  intros.
  intro.
  unfold boundsnCon in H.
  decompose record H.
  apply app_cons_not_nil in H0.
  contradiction.
  destruct a.
  destruct p.
  assert ({c = c0} + {c <> c0}) by (apply eq_con).
  destruct H.
  rewrite e.
  left.
  exists s.
  exists nil.
  exists sS.
  split.
  auto.
  intros.
  intro.
  inversion H.
  destruct IHsS.
  left.
  destruct s0.
  exists x.
  unfold boundsnCon in b.
  decompose record b.
  exists (inl (c0, s) :: x0).
  exists x1.
  rewrite H.
  split.
  auto.
  intros.
  intro.
  inversion H0.
  inversion H2.
  apply n; auto.
  apply H1 with tau'; auto.
  right.
  intros.
  intro.  
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  apply n; auto.
  assert (sS = x ++ inl (c, tau) :: x0).
  inversion H0.
  auto.
  apply n0 with tau.
  rewrite H1.
  exists x.
  exists x0.
  split.
  auto.
  intro.
  intro.
  apply H2 with tau'.
  right.
  assumption.
  (* inr cases *)
  destruct IHsS.
  left.
  destruct s.
  exists x.
  unfold boundsnCon in b.
  decompose record b.
  rewrite H.
  exists (inr p :: x0).
  exists x1.
  split.
  auto.
  intros.
  intro.
  apply H1 with tau'.
  inversion H0.
  inversion H2.
  assumption.
  (* not bound at all *)
  right.
  intros.
  intro.
  apply n with tau.
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  inversion H0.
  exists x.
  exists x0.
  split.
  auto.
  intros.
  intro.
  apply H2 with tau'.
  right.
  assumption.
Qed.  

(** determianacy of boundsnCon **)

Lemma boundsnCon_weak_r:
  forall (sS : snsgn) (c : con) (a : tcon) (tau : snTy) (kappa : snK),
    boundsnCon c tau (inr (a , kappa) :: sS) ->
    boundsnCon c tau sS.
Proof.
  intros.
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  exists x.
  exists x0.
  inversion H0.
  split.
  auto.
  intros.
  intro.
  apply H2 with tau'.
  right.
  assumption.
Qed.  

Lemma boundsnCon_weak_l:
  forall (sS : snsgn) (c d : con) (tau1 tau2 : snTy),
    boundsnCon c tau1 (inl (d , tau2) :: sS) ->
    c <> d ->
    boundsnCon c tau1 sS.
Proof.
  intros.
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  destruct H0.
  symmetry; assumption.
  exists x.
  exists x0.
  inversion H1.
  split.
  auto.
  intros.
  intro.
  apply H3 with tau'.
  right.
  assumption.
Qed.  

Lemma boundsnCon_weak_determinacy:
  forall (sS : snsgn) (c : con) (tau1 tau2 : snTy),
    boundsnCon c tau1 (inl (c, tau2) :: sS) ->
    ~ indomsnCon c sS
    -> tau1 = tau2.
Proof.
  intros.
  unfold boundsnCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  reflexivity.
  destruct H0.
  exists tau1.
  exists x.
  exists x0.
  split.
  inversion H1.
  reflexivity.
  intros; intro.
  apply H3 with tau'.
  right.
  assumption.
Qed.

Lemma boundsnCon_determinacy:
  forall (sS : snsgn) (a : tcon) (tau1 tau2 : snTy),
    wfssig_nl sS ->
    boundsnCon a tau1 sS ->
    boundsnCon a tau2 sS ->
    tau1 = tau2.
Proof.
  intros.
  induction H.
  (* nil case *)
  intros.
  unfold boundsnCon in H0.
  decompose record H0.
  apply app_cons_not_nil in H.
  contradiction.
  (* step case *)
  intros.
  apply IHwfssig_nl; eapply boundsnCon_weak_r ; eauto.
  (* *)
  assert ({c = a} + {c <> a}) by (apply eq_con).
  destruct H3.
  rewrite <- e in H0.
  rewrite <- e in H1.
  assert (tau1 = tau).
  eauto using boundsnCon_weak_determinacy; auto.
  assert (tau2 = tau).
  eauto using boundsnCon_weak_determinacy; auto.
  rewrite H3.
  rewrite H4.
  reflexivity.
  apply IHwfssig_nl; eauto using boundsnCon_weak_l; auto.
Qed.
 *)

(**
  * boundTCon
 **)

(** decidability of boundnTCon **)

Lemma boundTCon_dec :
  forall (S : sgn) (a : tcon),
  {L : _ | boundTCon a L S} + {(forall L, ~ boundTCon a L S)}.
Proof.
  (intros **).
  (induction S).
  - 
    right.
    (intros **).
    intro.
    (unfold boundTCon in H).
    decompose record H.
    (apply app_cons_not_nil in H0).
    contradiction.
  - (destruct a0; destruct p).
    + (* inl - inr case *)
      (destruct IHS).
      * left.
        (destruct s0).
        exists x.
        (unfold boundTCon in b).
        decompose record b.
        (unfold boundTCon).
        (simpl).
        (rewrite H).
        exists (inl (c, proj1_sig s) :: x0).
        exists x1.
        split.
        auto.
        (intros **).
        intro.
        (apply H1).
        (inversion H0).
        (inversion H2).
        assumption.
      * (* not bound at all *)
        right.
        (intros **).
        intro.
        (apply n with L).
        (unfold boundTCon in H).
        decompose record H.
        (destruct x).
        (inversion H0).
        (inversion H0).
        exists x.
        exists x0.
        split.
        auto.
        (intros **).
        intro.
        (apply H2).
        right.
        assumption. 
    + (* inr - inr case *)
      (destruct s).
      (assert ({t = a} + {t <> a}) by apply eq_tcon).
      (destruct H).
      * (rewrite e).
        left.
        exists x.
        exists nil.
        exists (map castSig S).
        split.
        auto.
        (intros **).
        intro.
        (inversion H).
      * (destruct IHS).
        { left.
          (destruct s).
          exists x0.
          (unfold boundTCon in b).
          decompose record b.
          (simpl).
          exists (inr (t, x) :: x1).
          exists x2.
        (simpl).
        (rewrite H).
        split.
        eauto.
        (intros **).
        intro.
        (inversion H0).
        (inversion H2).
        (apply n; auto).
        (apply H1; auto).
        }
        { right.
          (intros **).
          intro.  
          (unfold boundTCon in H).
          decompose record H.
          (destruct x0).
          (inversion H0).
          (apply n; auto).
          (simpl in H0).
          (assert (map castSig S = x0 ++ inr (a, L) :: x1)).
          (inversion H0).
          auto.
          (apply n0 with L).
          (unfold boundTCon).
          (rewrite H1).
          exists x0.
          exists x1.
          split.
          auto.
          (intros **).
          intro.
          (apply H2).
          right.
          assumption.
        }
Defined.  

(** determianacy of boundTCon **)

Lemma boundTCon_weak_l :
  forall (S : sgn) (c a : tcon) (A : {eTy : _ | is_Ty_of_eTy eTy}) (L : eK),
  boundTCon a L (inl (c, A) :: S) -> boundTCon a L S.
Proof.
  (intros **).
  (unfold boundTCon in H).
  decompose record H.
  (destruct x).
  (inversion H0).
  exists x.
  exists x0.
  (inversion H0).
  split.
  auto.
  (intros **).
  intro.
  (apply H2).
  right.
  assumption.
Qed.  

Lemma boundnTCon_weak_r :
  forall (S : sgn) (a b : tcon) (L : eK) (K : {eK : _ | is_K_of_eK eK}),
  boundTCon a L (inr (b, K) :: S) -> a <> b -> boundTCon a L S.
Proof.
  (intros **).
  (unfold boundTCon in H).
  decompose record H.
  (destruct x).
  (inversion H1).
  (destruct H0).
  (symmetry; assumption).
  exists x.
  exists x0.
  (inversion H1).
  split.
  auto.
  (intros **).
  intro.
  (apply H3).
  right.
  assumption.
Qed.  

(*
Lemma boundnTCon_weak_determinacy:
  forall (S : sgn) (a : tcon) (L1 L2 : eK),
    boundnTCon a L1 (inr (a, L2) :: S) ->
    ~ indomnTCon a S
    -> L1 = L2.
Proof.
  intros.
  unfold boundnTCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  reflexivity.
  destruct H0.
  exists L1.
  exists x.
  exists x0.
  split.
  inversion H1.
  reflexivity.
  intros; intro.
  apply H3 with nL'.
  right.
  assumption.
Qed.
 *)

(*
Lemma boundnTCon_determinacy:
  forall (S : sgn) (a : tcon) (L1 L2 : eK),
    wfsig_nl S ->
    boundTCon a L1 S ->
    boundTCon a L2 S ->
    L1 = L2.
Proof.
  intros.
  induction H.
  (* nil case *)
  intros.
  unfold boundnTCon in H0.
  decompose record H0.
  apply app_cons_not_nil in H.
  contradiction.
  (* step case *)
  intros.
  (* *)
  assert ({a = a0} + {a <> a0}) by (apply eq_tcon).
  destruct H4.
  rewrite e in H0.
  rewrite e in H1.
  assert (L1 = nL).
  eauto using boundnTCon_weak_determinacy; auto.
  assert (L2 = nL).
  eauto using boundnTCon_weak_determinacy; auto.
  rewrite H4.
  rewrite H5.
  reflexivity.
  (* *)
  eauto using boundnTCon_weak_r; auto.
  apply IHwfsig_nl; eauto using boundnTCon_weak_l.  
Qed.
 *)

(**
  * boundsnTCon
 **)

(** decidability of boundsnTCon **)

(*
Lemma boundsnTCon_dec:
  forall (sS : snsgn) (a : tcon),
    {kappa | boundsnTCon a kappa sS} + {forall kappa , ~ boundsnTCon a kappa sS}.
Proof.
  intros.
  induction sS.
  right.
  intros.
  intro.
  unfold boundsnTCon in H.
  decompose record H.
  apply app_cons_not_nil in H0.
  contradiction.
  destruct a0.
  (* inl cases *)
  destruct IHsS.
  left.
  destruct s.
  exists x.
  unfold boundsnTCon in b.
  decompose record b.
  rewrite H.
  exists (inl p :: x0).
  exists x1.
  split.
  auto.
  intros.
  intro.
  apply H1 with kappa'.
  inversion H0.
  inversion H2.
  assumption.
  (* not bound at all *)
  right.
  intros.
  intro.
  apply n with kappa.
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  inversion H0.
  exists x.
  exists x0.
  split.
  auto.
  intros.
  intro.
  apply H2 with kappa'.
  right.
  assumption.
  (* int cases *)  
  destruct p.
  assert ({a = t} + {a <> t}) by (apply eq_con).
  destruct H.
  rewrite e.
  left.
  exists s.
  exists nil.
  exists sS.
  split.
  auto.
  intros.
  intro.
  inversion H.
  destruct IHsS.
  left.
  destruct s0.
  exists x.
  unfold boundsnTCon in b.
  decompose record b.
  exists (inr (t, s) :: x0).
  exists x1.
  rewrite H.
  split.
  auto.
  intros.
  intro.
  inversion H0.
  inversion H2.
  apply n; auto.
  apply H1 with kappa'; auto.
  right.
  intros.
  intro.  
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  apply n; auto.
  assert (sS = x ++ inr (a, kappa) :: x0).
  inversion H0.
  auto.
  apply n0 with kappa.
  rewrite H1.
  exists x.
  exists x0.
  split.
  auto.
  intro.
  intro.
  apply H2 with kappa'.
  right.
  assumption.
Qed.
  
(** determianacy of boundsnTCon **)

Lemma boundsnTCon_weak_l:
  forall (sS : snsgn) (c : con) (a : tcon) (tau : snTy) (kappa : snK),
    boundsnTCon a kappa (inl (c , tau) :: sS) ->
    boundsnTCon a kappa sS.
Proof.
  intros.
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H0.
  exists x.
  exists x0.
  inversion H0.
  split.
  auto.
  intros.
  intro.
  apply H2 with kappa'.
  right.
  assumption.
Qed.  

Lemma boundsnTCon_weak_r:
  forall (sS : snsgn) (a b : tcon) (kappa1 kappa2 : snK),
    boundsnTCon a kappa1 (inr (b , kappa2) :: sS) ->
    a <> b ->
    boundsnTCon a kappa1 sS.
Proof.
  intros.
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  destruct H0.
  symmetry; assumption.
  exists x.
  exists x0.
  inversion H1.
  split.
  auto.
  intros.
  intro.
  apply H3 with kappa'.
  right.
  assumption.
Qed.  

Lemma boundsnTCon_weak_determinacy:
  forall (sS : snsgn) (a : tcon) (kappa1 kappa2 : snK),
    boundsnTCon a kappa1 (inr (a, kappa2) :: sS) ->
    ~ indomsnTCon a sS
    -> kappa1 = kappa2.
Proof.
  intros.
  unfold boundsnTCon in H.
  decompose record H.
  destruct x.
  inversion H1.
  reflexivity.
  destruct H0.
  exists kappa1.
  exists x.
  exists x0.
  split.
  inversion H1.
  reflexivity.
  intros; intro.
  apply H3 with kappa'.
  right.
  assumption.
Qed.
  
Lemma boundsnTCon_determinacy:
  forall (sS : snsgn) (a : tcon) (kappa1 kappa2 : snK),
    wfssig_nl sS ->
    boundsnTCon a kappa1 sS ->
    boundsnTCon a kappa2 sS ->
    kappa1 = kappa2.
Proof.
  intros.
  induction H.
  (* nil case *)
  intros.
  unfold boundsnTCon in H0.
  decompose record H0.
  apply app_cons_not_nil in H.
  contradiction.
  (* step case *)
  intros.
  (* *)
  assert ({a = a0} + {a <> a0}) by (apply eq_tcon).
  destruct H3.
  rewrite e in H0.
  rewrite e in H1.
  assert (kappa1 = kappa).
  eauto using boundsnTCon_weak_determinacy; auto.
  assert (kappa2 = kappa).
  eauto using boundsnTCon_weak_determinacy; auto.
  rewrite H3.
  rewrite H4.
  reflexivity.
  (* *)
  eauto using boundsnTCon_weak_r; auto.
  apply IHwfssig_nl; eauto using boundsnTCon_weak_l.  
Qed.

 *)

(**  checking of boundsnTcon **)

(*
Lemma boundsnTCon_check:
  forall (sS : snsgn) (a : tcon) (kappa : snK),
    wfssig_nl sS ->
    {boundsnTCon a kappa sS} + {~ boundsnTCon a kappa sS}.
Proof.
  intros.
  assert ({ kappa' | boundsnTCon a kappa' sS} +
          { forall kappa', ~ boundsnTCon a kappa' sS})
    as [ [kappa'] | ]
      by (apply boundsnTCon_dec).
  - assert ({kappa = kappa'} + {kappa <> kappa'})
      as [ eq_kappa | ]
        by ( apply eq_snK).
    + (* kappa = kappa' *)
      rewrite eq_kappa.
      left; auto.
    + (* kappa <> kappa' *)
      right; intro Hb.
      assert (kappa = kappa')
        by (eauto using boundsnTCon_determinacy).
      contradiction.
  - right; intro.
    eapply n; eauto.
Qed.

(*  
(** erausre stability for TCon **)
Lemma indomsnTCon_stable:
  forall (S : nsgn) (a : tcon),
    indomsnTCon a (erasure_nsgn S) ->
    indomnTCon a S.
Proof.
  
  intros S a.

  induction S.

  - intro H.
    unfold indomsnTCon in H.
    unfold boundsnTCon in H.
    decompose record H.
    cbn in H1.
    apply app_cons_not_nil in H1.
    contradiction.

  - destruct a0.
    destruct p.
    cbn.

    intro H.

    assert (indomnTCon a S).
    apply IHS.
    
    unfold indomsnTCon.
    unfold boundsnTCon.
    unfold indomsnTCon in H.
    unfold boundsnTCon in H.

    decompose record H.
    exists x.

    destruct x0.
    cbn in H1; inversion H1.

    exists x0.
    exists x1.

    cbn in H1.
    inversion H1.
    split; auto.
    intros; intro.
    eapply H2.
    right; eauto.

    unfold indomnTCon in H0.
    unfold boundnTCon in H0.
    decompose record H0.

    unfold indomnTCon.
    unfold boundnTCon.
    exists x.
    exists (inl (c, n) :: x0).
    exists x1.
    split.
    cbn.
    f_equal; auto.

    intros; intro.
    eapply H3.
    destruct H1.
    inversion e.
    eauto.

    destruct p.
    cbn.

    assert ({t = a} + {t <> a}) as [ | ] by (apply eq_tcon).

    + rewrite e.
      intros.
      unfold indomnTCon.
      unfold boundnTCon.

      exists n.
      exists nil.
      exists S.
      split.
      cbn; auto.
      intros; intro.
      inversion H0.

    + intros.
      assert (indomnTCon a S).
      apply IHS.

      unfold indomsnTCon in H.
      unfold boundsnTCon in H.
      decompose record H.

      destruct x0.
      cbn in H1.
      inversion H1.
      contradiction.

      unfold indomsnTCon.
      unfold boundsnTCon.
      exists x. 
      exists x0.
      exists x1.

      split.
      cbn in H1.
      inversion H1.
      auto.

      intros; intro.
      eapply H2.
      right; eauto.

      unfold indomnTCon in H0.
      unfold boundnTCon in H0.
      decompose record H0.

      unfold indomnTCon.
      unfold boundnTCon.
      exists x.
      exists (inr (t, n) :: x0).
      exists (x1).
      split.
      cbn.
      f_equal; auto.
      intros; intro.
      eapply H3.
      destruct H1.
      inversion e; contradiction.
      eauto.
Qed.

(** * Stability if indomsnCon and indomsnTCon * **)
  
(** erausre stability for con **)
Lemma indomsnCon_stable:
  forall (S : nsgn) (c : con),
    indomsnCon c (erasure_nsgn S) ->
    indomnCon c S.
Proof. 
  intros S a; 
  unfold indomsnCon;
  unfold boundsnCon;
  unfold indomnCon;
  unfold boundnCon.
  induction S.
  
  - intro H.
    decompose record H.
    cbn in H1.
    apply app_cons_not_nil in H1.
    contradiction.

  - destruct a0; destruct p;
    cbn.

    + assert ({c = a} + {c <> a}) as [ | ] by (apply eq_con).
    
      * rewrite e.
        intros.
        
        exists n.
        exists nil.
        exists S.
        split.
        cbn; auto.
        intros; intro.
        inversion H0.

      * intros.
        assert (indomnCon a S).
        
        { apply IHS.
          decompose record H.

          destruct x0.
          cbn in H1.
          inversion H1.
          contradiction.

          exists x. 
          exists x0.
          exists x1.

          split.
          cbn in H1.
          inversion H1.
          auto. 

          intros; intro.
          eapply H2.
          right; eauto. }

      unfold indomnCon in H0.
      unfold boundnCon in H0.
      decompose record H0.

      exists x.
      exists (inl (c, n) :: x0).
      exists (x1).
      split.
      cbn.
      f_equal; auto.
      intros; intro.
      eapply H3.
      destruct H1.
      inversion e; contradiction.
      eauto.

    + 
    intro H.
    decompose record H.

    assert (indomnCon a S).
    { apply IHS.   
      
      exists x.
      destruct x0.
      cbn in H1; inversion H1.

      exists x0.
      exists x1.

      cbn in H1.
      inversion H1.
      split; auto.
      intros; intro.
      eapply H2.
      right; eauto. }

    unfold indomnCon in H0.
    unfold boundnCon in H0.
    decompose record H0.

    exists x2.
    exists (inr (t, n) :: x3).
    exists x4.
    split.
    cbn.
    f_equal; auto.

    intros; intro.
    eapply H5.
    destruct H3.
    inversion e.
    eauto.
Qed.

*)

*)     