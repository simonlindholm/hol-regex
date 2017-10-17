open HolKernel Parse boolLib bossLib;

val _ = new_theory "regex";

open listTheory rich_listTheory pairTheory pairSimps pred_setTheory;

(** Definition of a regex. **)

val _ = Datatype `Reg = Eps | Sym 'a | Alt Reg Reg | Seq Reg Reg | Rep Reg`;

(** Set-theoretic definition of what a regex matches. This is our ground truth. **)

val language_of = Define `
  (language_of (Eps : 'a Reg) = {[]}) ∧
  (language_of (Sym x) = {[x]}) ∧
  (language_of (Alt a b) = language_of a ∪ language_of b) ∧
  (language_of (Seq a b) = {(x ++ y) | x ∈ language_of a ∧ y ∈ language_of b}) ∧
  (language_of (Rep a) = {FLAT li | ∀x. MEM x li ⇒ x ∈ language_of a}) `;

(** Naive, but executable, regex matcher. **)

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

(** Some tests **)
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

(** Basic lemmata **)

val SPLIT_EMPTY1 = store_thm ("SPLIT_EMPTY1",
  ``∀ (a : 'a list). MEM ([], a) (split a)``,
  Cases >> SIMP_TAC list_ss [split]);

val SPLIT_SOUND = store_thm ("SPLIT_SOUND",
  ``∀ x y (w : 'a list). MEM (x, y) (split w) ⇒ (x ++ y = w)``,
  Induct_on `w` >| [
    SIMP_TAC list_ss [split],
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC list_ss [split, MEM_MAP, PAIR_MAP]
  ]);

val SPLIT_COMPLETE = store_thm ("SPLIT_COMPLETE",
  ``∀ a (b : 'a list). MEM (a, b) (split (a ++ b))``,
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

val PARTS_SOUND = store_thm ("PARTS_SOUND",
  ``∀ (li : 'a list) part. MEM part (parts li) ⇒ (FLAT part = li)``,
  Induct >| [
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC list_ss [parts],

    REPEAT STRIP_TAC >>
    Cases_on `li` >>
    FULL_SIMP_TAC list_ss [parts, MEM_MAP] >>

    `FLAT y = h'::t` by ASM_SIMP_TAC bool_ss[] >>
    Cases_on `y` >- FULL_SIMP_TAC list_ss [FLAT] >>

    FULL_SIMP_TAC list_ss [add_to_head]
  ]);

(* We'd want to say that parts is also complete in the sense that if we flatten
 * an arbitrary list, parts will recover (among else) that list. But that isn't
 * quite true, because we skip empty parts. Instead we settle for showing that
 * parts recovers a *subset* of the original list -- for our purposes, we don't
 * need it to be ordered. *)
val PARTS_IN_FLAT = store_thm ("PARTS_IN_FLAT",
  ``∀ li. ∃ part. MEM part (parts (FLAT li)) ∧
    ∀ (x : 'a list). MEM x part ⇒ MEM x li``,
  Induct >| [
    EXISTS_TAC ``[] : 'a list list`` >>
    ASM_SIMP_TAC list_ss [FLAT, parts],

    FULL_SIMP_TAC bool_ss [] >>
    Cases >| [
      EXISTS_TAC ``part : 'a list list`` >>
      ASM_SIMP_TAC list_ss [],

      EXISTS_TAC ``((h'::t) :: part) : 'a list list`` >>
      REPEAT STRIP_TAC >| [
        WEAKEN_TAC is_forall >>
        ASM_SIMP_TAC list_ss [] >>

        (* Generalize "FLAT li" to any list *)
        `∃ rest. FLAT li = rest` by ASM_SIMP_TAC bool_ss[] >>
        FULL_SIMP_TAC bool_ss[] >>
        WEAKEN_TAC is_eq >>

        ID_SPEC_TAC ``h' : 'a`` >>
        Induct_on `t` >| [
          ASM_SIMP_TAC list_ss [] >>
          Cases_on `rest` >>
          FULL_SIMP_TAC list_ss [parts, add_to_head] >>
          Cases_on `t` >>
          FULL_SIMP_TAC list_ss [parts, add_to_head, MEM_MAP] >>
          METIS_TAC[parts, add_to_head],

          FULL_SIMP_TAC list_ss [parts, add_to_head] >>
          METIS_TAC[parts, add_to_head, MEM_MAP]
        ],

        FULL_SIMP_TAC list_ss []
      ]
    ]
  ]);

val ACCEPT_SEQ_CONCAT = store_thm ("ACCEPT_SEQ_CONCAT",
  ``∀ p q u (v : 'a list).
    accept p u ∧ accept q v ⇒ accept (Seq p q) (u ++ v)``,
  REPEAT STRIP_TAC >>
  SIMP_TAC list_ss [accept, EXISTS_MEM] >>
  EXISTS_TAC ``(u : 'a list, v : 'a list)`` >>
  ASM_SIMP_TAC std_ss [SPLIT_COMPLETE]);

val ACCEPT_REP_NIL = store_thm ("ACCEPT_REP_NIL",
  ``∀ (p : 'a Reg). accept (Rep p) []``,
  SIMP_TAC list_ss [accept, parts]);

(** Equivalence with language **)

val set_ss = std_ss ++ SET_SPEC_ss;

val ACCEPT_IN_LANG = prove (
  ``∀ (r : 'a Reg) w. accept r w ⇒  w ∈ (language_of r)``,
  Induct >> REPEAT STRIP_TAC >>
  FULL_SIMP_TAC set_ss [language_of, accept, IN_SING, IN_UNION, NULL] >| [
    Cases_on `w` >> FULL_SIMP_TAC list_ss [],

    FULL_SIMP_TAC (std_ss ++ gen_beta_ss) [EXISTS_MEM] >>
    EXISTS_TAC ``FST (e : 'a list # 'a list)`` >>
    EXISTS_TAC ``SND (e : 'a list # 'a list)`` >>
    ASM_SIMP_TAC std_ss [SPLIT_SOUND],

    FULL_SIMP_TAC std_ss [EXISTS_MEM, EVERY_MEM] >>
    EXISTS_TAC ``e : 'a list list`` >>
    FULL_SIMP_TAC std_ss [PARTS_SOUND]
  ]);

val LANG_IN_ACCEPT = prove (
  ``∀ (r : 'a Reg) w. w ∈ (language_of r) ⇒ accept r w``,
  Induct >> REPEAT STRIP_TAC >>
  FULL_SIMP_TAC set_ss [language_of, accept, IN_SING, IN_UNION, NULL] >| [
    METIS_TAC [accept, ACCEPT_SEQ_CONCAT],

    `∃ part. MEM part (parts (FLAT li)) ∧ ∀ x. (MEM x part ⇒ MEM x li)`
      by REWRITE_TAC [PARTS_IN_FLAT] >>
    SIMP_TAC list_ss [EXISTS_MEM] >>
    EXISTS_TAC ``(part : 'a list list)`` >>
    ASM_SIMP_TAC std_ss [EVERY_MEM]
  ]);

val ACCEPT_CORRECT = store_thm ("ACCEPT_CORRECT",
  ``∀ (r : 'a Reg) w. accept r w ⇔ w ∈ (language_of r)``,
  REPEAT STRIP_TAC >>
  EQ_TAC >>
  REWRITE_TAC [ACCEPT_IN_LANG, LANG_IN_ACCEPT]);

val _ = export_theory();
