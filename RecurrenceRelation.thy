(*
  Recurrence Relation of BFS

  Isabelle 2014

  Copyright (c) 2020 Hisabumi Hatsugai
*)
theory RecurrenceRelation
imports "~~/src/HOL/Hoare/Hoare_Logic"
begin

typedecl state
consts a :: state                (* initial state *)
consts R :: "(state * state)set" (* directed edges *)

(*
  s n: set of nodes visited on the n-th step
  f n: frontier on the n-th step
*)
fun s :: "nat => state set" and f :: "nat => state set" where
    "s 0       = {}"
  | "s (Suc n) = (s n) Un (f n)"
  | "f 0       = {a}"
  | "f (Suc n) = R `` (f n) - ((s n) Un (f n))"

(*
  s n = {a} ∪ R({a}) ∪ R^2({a}) ∪ ... ∪ R^(n-1)({a})
  f n = R^n({a}) - s(n)
*)
lemma
  "s k = Union{(R^^j) `` {a}|j. j < k}
  & f k = (R^^k) `` {a} - s k"
apply(induct_tac k)
apply(auto)
apply (metis Image_singleton_iff less_Suc_eq)
apply (metis Image_singleton_iff less_Suc_eq)
apply(subgoal_tac "y ~: s n")
apply(rule_tac a="y" in ImageI)
apply(assumption)
apply(clarsimp)
apply(auto)
apply(subgoal_tac "(a, z): R^^(Suc j)")
apply(clarsimp)
apply(case_tac "Suc j = n")
apply(clarsimp)
apply (metis relpow.simps(2) relpow_Suc_I)
apply(drule_tac x="(R ^^ (Suc j)) `` {a}" in spec)
apply(clarsimp)
apply(erule disjE)
apply(drule_tac x="Suc j" in spec)
apply(clarsimp)
apply (metis (full_types) relpow.simps(2) relpow_Suc_I)
by (metis relpow_Suc_I)

end
