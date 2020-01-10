(*
  Correctness of BFS

  Isabelle 2014

  Copyright (c) 2020 Hisabumi Hatsugai
*)

theory CorrectnessBFS
imports "~~/src/HOL/Hoare/Hoare_Logic"
begin

lemma l0 [rule_format]:
  "[| (a, x) : r^*; r `` s <= s Un f |] ==>
   (a : s | a : f) -->
   x : s Un f Un r^* `` (r `` f - (s Un f))"
apply(erule converse_rtrancl_induct)
apply(auto)
done

(*
  R: directed edges
  a: initial node
  s: set of nodes visited
  f: frontier
*)
theorem
  "VARS s f
  {True}
  s := {};
  f := {a};
  WHILE f ~= {}
  INV {
    s Un R^* `` f = R^* `` {a} &
    R `` s <= s Un f &
    a : s Un f
  }
  DO
    s := s Un f;
    f := R `` f - s
  OD
  {s = R^* `` {a}}"

apply(vcg)
apply(auto intro: transitive_closure_trans)
apply(drule_tac x=xa and s=s and f=f in l0)
apply(auto)
apply(drule_tac x=xa and s=s and f=f in l0)
apply(auto)
done

end
