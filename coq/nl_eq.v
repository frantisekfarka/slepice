Require Import List.

Require Import defns.

Require Import nl_fusion.

(**
   * Standard equality
 **)

(** decidability of equality for nameless syntax **)

Lemma eq_nTy_dec:
  forall (A B : nTy),
    {A = B} + {A <> B}
with eq_nte_dec:
  forall (M N : nte),
    {M = N} + {M <> N}.
Proof.
  (* lemma 1 *)
  intros.
  decide equality.
  apply eq_tcon.
  (* lemma 2 *)
  intros.
  decide equality.
  apply eq_con.
  decide equality.
  decide equality.
Qed.

Lemma eq_snTy_dec:
  forall (tau1 tau2 : snTy),
    {tau1 = tau2} + {tau1 <> tau2}.
Proof.
  intros.
  decide equality.
  apply eq_tcon.
Qed.  

Lemma eq_nK:
  forall (K L : nK),
    {K = L} + {K <> L}.
Proof.
  decide equality.
  apply eq_nTy_dec.
Qed.

Lemma eq_snK:
  forall (kappa1 kappa2 : snK),
    {kappa1 = kappa2} + {kappa1 <> kappa2}.
Proof.
  decide equality.
  apply eq_snTy_dec.
Qed.
  
(** equality under erasure w.r.t context shifting **)

Lemma eq_nTy_erasure:
  forall (A A' : nTy) (i : Ixc),
    cs_nTy A i A' ->
    (erasure_nTy A) = (erasure_nTy A').
Proof.
  intros.
  induction H; auto.
  cbv; f_equal.
  apply IHcs_nTy1.
  apply IHcs_nTy2.
Qed.

(*
Lemma eq_nctx_cs_erasure:
  forall (G G' : nctx) (i : Ixc) (A : nTy),
    cs_nctx G i A G' ->
    cs_snctx (erasure_nctx G) i (erasure_nTy A) (erasure_nctx G').
Proof.
  intros.
  induction H.
  cbv; constructor.
  cbv; f_equal.
  cbv.
  eapply IHcs_nctx.
  econstructor.
  apply eq_nTy_erasure; auto.
  apply IHcs_nctx.
Qed.  
 *)

