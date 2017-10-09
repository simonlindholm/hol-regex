open HolKernel Parse boolLib bossLib;

val _ = new_theory "regex";

open listTheory rich_listTheory pairTheory pred_setTheory;
open EmitML;

val ERR = mk_HOL_ERR "regex";

val _ = Datatype `Reg = Eps | Sym 'a | Alt Reg Reg | Seq Reg Reg | Rep Reg`;

val language_of = Define `
  (language_of (Eps : 'a Reg) = {[]}) ∧
  (language_of (Sym x) = {[x]}) ∧
  (language_of (Alt a b) = language_of a ∪ language_of b) ∧
  (language_of (Seq a b) = {(x ++ y) | x ∈ language_of a ∧ y ∈ language_of b}) ∧
  (language_of (Rep a) = {FLAT li | ∀x. MEM x li ⇒ x ∈ language_of a}) `;

val split = Define `
  (split ([] : 'a list) = [([], [])]) ∧
  (split (c :: cs) = ([], c :: cs) :: MAP (CONS c ## I) (split cs)) `;

val add_to_head = Define `
  (add_to_head (c : 'a) (x :: xs) = (c :: x) :: xs)`;

val parts = Define `
  (parts ([] : 'a list) = [[]]) ∧
  (parts [c] = [[[c]]]) ∧
  (parts (c :: cs) = MAP (CONS [c]) (parts cs) ++ MAP (add_to_head c) (parts cs)) `;

val accept = Define `
  (accept (Eps : 'a Reg) u = NULL u) ∧
  (accept (Sym c) u = (u = [c])) ∧
  (accept (Alt p q) u = accept p u ∨ accept q u) ∧
  (accept (Seq p q) u = EXISTS (λ(x,y). accept p x ∧ accept q y) (split u)) ∧
  (accept (Rep r) u = EXISTS (EVERY (accept r)) (parts u)) `;

(* sanity check lemmata *)

(*
val IS_WEAK_SUBLIST_REC = store_thm ("IS_WEAK_SUBLIST_REC",
  ``∀ a a' t t'. (IS_WEAK_SUBLIST_REC t []) ∧
  ~(IS_WEAK_SUBLIST_REC [] (a::t)) ∧
  (IS_WEAK_SUBLIST_REC (a::t) (a::t') = IS_WEAK_SUBLIST_REC t t') ∧
  (a ≠ a' ⇒ (IS_WEAK_SUBLIST_REC (a::t) (a'::t') =
    IS_WEAK_SUBLIST_REC t (a'::t')))``,
SIMP_TAC bool_ss [IS_WEAK_SUBLIST_REC_def]);


(* Some tests *)
val test1 = EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4;5;6;7] [2;5;6]``;
val test2 = EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4;5;6;7] [2;6;5]``;
val test3 = EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4;5;6;7] [2;5;6;8]``;
*)

val _ = export_theory();
