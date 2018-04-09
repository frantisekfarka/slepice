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


Extract Inductive Defns.eTy =>  "eTy" [ "Ety_tcon"
                                         "Ety_pi_intro"
                                         "Ety_pi_elim"
                                         "Ety_mtvar"
                                         "Ety_tvar"
                                     ].

Extract Inductive Defns.ete =>  "ete" [ "Ete_con"
                                         "Ete_ix"
                                         "Ete_pi_intro"
                                         "Ete_pi_elim"
                                         "Ete_mvar"
                                         "Ete_tvar"
                                     ].

Extract Inductive Defns.eK =>  "eK" [ "Ek_type"
                                       "Ek_pi_intro"
                                       "Ek_mkvar"
                                       "Ek_tvar"
                                   ].

Extract Inductive Defns.TTAtom => "ttAtom" [ (* atom in TT *)
  "Ttat_true" "Ttat_eq_te" "Ttat_eq_Ty" "Ttat_eq_K" "Ttat_Ty"
              "Ttat_te" "Ttat_shiftK" "Ttat_substK" "Ttat_shiftTy" "Ttat_substTy"
              "Ttat_shiftte" "Ttat_substte" ].

Extract Inductive Defns.TTGoal => "tTGoal" [ (* goal in TT *)
  "Ttgoal_conj" "Ttgoal_bound_at" "Ttgoal_unbound_at" ].

Extract Inductive Defns.TTProg => "tTProg" [ (* program in TT *)
           "Ttprog_empty" "Ttprog_hc_con" "Ttprog_hc_nob" ].


Extract Inductive Defns.list_TTAtom => "list" [ "[]" "(::)" ].


(* extracted librarires *)
Extraction Library Datatypes.
Extraction Library Specif.
Extraction Library Defns.
Extraction Library Eq.
Extraction Library Sgn.
Extraction Library Refin.

