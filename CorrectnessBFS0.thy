(*
  Correctness of BFS (no guarantee of termination)

  Isabelle 2014

  Copyright (c) 2020 Hisabumi Hatsugai
*)

theory CorrectnessBFS0
imports "~~/src/HOL/Hoare/Hoare_Logic"
begin

(*
  simple but no guarantee of termination

  R: directed edges
  a: initial node
  s: set of nodes visited
  f: frontier
*)
lemma
  "VARS s f
  {True}
  s := {};
  f := {a};
  WHILE f ~= {}
  INV { s Un R^* `` f = R^* `` {a} }
  DO
    s := s Un f;
    f := R `` f
  OD
  {s = R^* `` {a}}"
apply(vcg)
apply(auto)
apply (metis ImageI Image_singleton_iff UnCI r_into_rtrancl rtrancl_trans)
by (metis Image_Id Image_singleton_iff UnE Un_Image equalityCE relcomp_Image rtrancl_trancl_reflcl trancl_unfold_left)

end
