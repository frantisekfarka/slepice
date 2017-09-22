Require Import defns.


Fixpoint struct_nTy_cs (A A' : nTy) (H : cs_nTy A A'):
  struct_nTy A = struct_nTy A'
with struct_nte_cs (M M' : nte) (H : cs_nte M M'):
  struct_nte M = struct_nte M'.
Proof.
  induction H.
  constructor.
  cbv; f_equal;  auto.
  cbv; f_equal; auto using struct_nte_cs.
  induction H.
  constructor.
  constructor.
  constructor.
  cbv; f_equal; auto using struct_nTy_cs.
  cbv; f_equal; auto.
Qed.

Fixpoint struct_nTy_cstu (A A' : nTy) (i : Ixc) (H : cstu_nTy A i A'):
  struct_nTy A = struct_nTy A'
with struct_nte_cstu (M M' : nte) (i : Ixc) (H : cstu_nte M i M'):
  struct_nte M = struct_nte M'.
Proof.
  induction H.
  constructor.
  cbv; f_equal; auto.
  cbv; f_equal; eauto using struct_nte_cstu.
  (* lemma 2 *)
  induction H.
  auto.
  auto.
  auto.
  auto.
  cbv; f_equal; eauto using struct_nTy_cstu.
  cbv; f_equal; auto.
Qed.

