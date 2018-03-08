Require Import Datatypes.
Require Import Specif.

Require Import Defns.
Require Import Eq.
Require Import Sgn.
Require Import Refin.

(* datytypes spec *)
Extraction Language Ocaml.
Extract Inductive list =>  "list" [  "[]"  "(::)" ].
Extract Inductive prod =>  "(*)" [  "(,)" ].
Extract Inductive nat =>  "int" [  "0"  "succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".


Extract Inductive bool =>  "bool" [  "true"  "false" ].
Extract Inductive sumbool =>  "bool" [  "true"  "false" ].


(* Extract Constant eq_con =>  "(==)". *)



(* ott definitions *)
Extract Constant Defns.Ix =>  "int".
Extract Inductive Defns.TTGoal =>  "tTGoal" [
  "Ttgoal_conj"  "Ttgoal_bound_at"  "Ttgoal_unbound_at" ].
Extract Inductive Defns.TTAtom =>  "tTAtom" [
  "Ttat_true"  "Ttat_eq_te"  "Ttat_eq_Ty"  "Ttat_eq_K"  "Ttat_Ty"  "Ttat_te" 
 "Ttat_shiftK"  "Ttat_substK"  "Ttat_shiftTy"  "Ttat_substTy" "Ttat_subste" "Ttat_shifte" ].


Extract Inductive Defns.eTy =>  "eTy" [
  "Typestar_nl_tcon"  "Typestar_nl_pi_intro"  "Typestar_nl_pi_elim" 
 "Typestar_nl_mtvar" ].

Extract Inductive Defns.ete =>  "ete" [
  "Termstar_nl_con"  "Termstar_nl_ix"  "Termstar_nl_pi_intro" 
 "Termstar_nl_pi_elim"  "Termstar_nl_mvar" ].

Extract Inductive Defns.eK =>  "eK" [
  "Kindstar_nl_type"  "Kindstar_nl_pi_intro"  "Kindstar_nl_mkvar" ].

Extract Inductive Defns.TTAtom => "ttAtom" [ (* atom in TT *)
  "Ttat_true" "Ttat_eq_te" "Ttat_eq_Ty" "Ttat_eq_K" "Ttat_Ty"
              "Ttat_te" "Ttat_shiftK" "Ttat_substK" "Ttat_shiftTy" "Ttat_substTy"
              "Ttat_shiftte" "Ttat_substte" ].

Extract Inductive Defns.TTGoal => "tTGoal" [ (* goal in TT *)
  "Ttgoal_conj" "Ttgoal_bound_at" "Ttgoal_unbound_at" ].

Extract Inductive Defns.TTProg => "tTProg" [ (* program in TT *)
           "Ttprog_empty" "Ttprog_hc_con" ].


Extract Inductive Defns.list_TTGoal => "list" [ "[]" "(::)" ].


(* extracted librarires *)
Extraction Library Datatypes.
Extraction Library Specif.
Extraction Library Defns.
Extraction Library Eq.
Extraction Library Sgn.
Extraction Library Refin.

