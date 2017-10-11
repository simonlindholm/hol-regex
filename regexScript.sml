open HolKernel Parse boolLib bossLib;

val _ = new_theory "regex";

open listTheory rich_listTheory pairTheory pred_setTheory;

(* Definition of a regex. *)

val _ = Datatype `Reg = Eps | Sym 'a | Alt Reg Reg | Seq Reg Reg | Rep Reg`;

(* Set-theoretic definition of what a regex matches. This is our ground truth. *)

val language_of = Define `
  (language_of (Eps : 'a Reg) = {[]}) ∧
  (language_of (Sym x) = {[x]}) ∧
  (language_of (Alt a b) = language_of a ∪ language_of b) ∧
  (language_of (Seq a b) = {(x ++ y) | x ∈ language_of a ∧ y ∈ language_of b}) ∧
  (language_of (Rep a) = {FLAT li | ∀x. MEM x li ⇒ x ∈ language_of a}) `;

(* Naive, but executable, regex matcher. *)

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

(* Some tests *)
fun assert_eq expected tm = let
  val tm2 = snd (dest_thm (EVAL tm));
  val rhs = snd (dest_eq tm2);
in
  if rhs <> expected then
    print ("Expected (" ^ (term_to_string tm) ^ ") to equal (" ^
    (term_to_string expected) ^ ") but was (" ^ (term_to_string rhs) ^ ")\n")
  else ()
end

val assert_true = assert_eq ``T``;
val assert_false = assert_eq ``F``;

assert_true ``accept (Eps : 'a Reg) []``;
assert_false ``accept Eps [1]``;
assert_false ``accept (Alt (Sym 1) (Sym 2)) []``;
assert_true ``accept (Alt (Sym 1) (Sym 2)) [1]``;
assert_false ``accept (Alt (Sym 1) (Sym 2)) [3]``;
assert_false ``accept (Alt (Sym 1) (Sym 2)) [1;1]``;
assert_false ``accept (Seq (Sym 1) (Sym 2)) []``;
assert_false ``accept (Seq (Sym 1) (Sym 2)) [1]``;
assert_true ``accept (Seq (Sym 1) (Sym 2)) [1;2]``;
assert_false ``accept (Seq (Sym 1) (Sym 2)) [1;1;2]``;
assert_true ``accept (Rep (Sym 1)) []``;
assert_true ``accept (Rep (Sym 1)) [1;1;1]``;
assert_false ``accept (Rep (Sym 1)) [1;2]``;

(* Basic lemmata *)

val SPLIT_EMPTY1 = store_thm ("SPLIT_EMPTY1",
  ``∀ a. MEM ([], a) (split a)``,
  Cases >> SIMP_TAC list_ss [split]);

val SPLIT_CONCAT = store_thm ("SPLIT_CONCAT",
  ``∀ a b. MEM (a, b) (split (a ++ b))``,
  Induct_on `a` >| [
    SIMP_TAC list_ss [split, SPLIT_EMPTY1],

    SIMP_TAC list_ss [split] >>
    `∀ (b : 'a list) (f : 'a list # 'a list -> 'a list # 'a list).
      MEM (f (a,b)) (MAP f (split (a ++ b)))`
        suffices_by (
          REPEAT STRIP_TAC >>
          `(h::a,b) = (CONS h ## I) (a,b)` by SIMP_TAC list_ss [] >>
          ASM_REWRITE_TAC[]
          ) >>
    ASM_SIMP_TAC list_ss[MEM_MAP] >>
    REPEAT STRIP_TAC >>
    EXISTS_TAC ``(a : 'a list, b : 'a list)`` >>
    ASM_SIMP_TAC bool_ss []
  ]);

val ACCEPT_SEQ_CONCAT = store_thm ("ACCEPT_SEQ_CONCAT",
  ``∀ p q u (v : 'a list).
    accept p u ∧ accept q v ⇒ accept (Seq p q) (u ++ v)``,
  REPEAT STRIP_TAC >>
  SIMP_TAC list_ss [accept, EXISTS_MEM] >>
  EXISTS_TAC ``(u : 'a list, v : 'a list)`` >>
  ASM_SIMP_TAC std_ss [SPLIT_CONCAT]);

val ACCEPT_REP_NIL = store_thm ("ACCEPT_REP_NIL",
  ``∀ (p : 'a Reg). accept (Rep p) []``,
  SIMP_TAC list_ss [accept, parts]);

val ACCEPT_REP_CONCAT = store_thm ("ACCEPT_REP_CONCAT",
  ``∀ p u (v : 'a list).
    accept p u ∧ accept (Rep p) v ⇒ accept (Rep p) (u ++ v)``,
    cheat);

(* Equivalence with language *)

val _ = export_theory();
