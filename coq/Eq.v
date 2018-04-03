Require Import List.

Require Import Defns.


(**
   * Standard equality
 **)

(** decidability of equality for nameless syntax **)

Lemma eq_eTy_dec : forall A B : eTy, {A = B} + {A <> B}
  with eq_ete_dec : forall M N : ete, {M = N} + {M <> N}.
Proof.
  (* lemma 1 *)
  (intros **).
  decide equality.
  (apply eq_tcon).
  decide equality.
  decide equality.
  (* lemma 2 *)
  (intros **).
  decide equality.
  (apply eq_con).
  decide equality.
  decide equality.
  decide equality.
Defined.

Lemma eq_sTy_dec : forall tau1 tau2 : sTy, {tau1 = tau2} + {tau1 <> tau2}.
Proof.
  (intros **).
  decide equality.
  (apply eq_tcon).
Defined.  

Lemma eq_eK : forall K L : eK, {K = L} + {K <> L}.
Proof.
  decide equality.
  (apply eq_eTy_dec).
  decide equality.
  decide equality.
Defined.

Lemma eq_sK :
  forall kappa1 kappa2 : sK, {kappa1 = kappa2} + {kappa1 <> kappa2}.
Proof.
  decide equality.
  (apply eq_sTy_dec).
Defined.
  
