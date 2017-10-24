open HolKernel Parse boolLib bossLib;

val _ = new_theory "regex";

open listTheory rich_listTheory pairTheory pairSimps boolSimps pred_setTheory patternMatchesSyntax;

(** Definition of a regex. **)

val _ = Datatype `Reg = Eps | Sym 'a | Alt Reg Reg | Seq Reg Reg | Rep Reg`;

(** Set-theoretic definition of what a regex matches. This is our ground truth. **)

val language_of_def = Define `
  (language_of (Eps : 'a Reg) = {[]}) ∧
  (language_of (Sym x) = {[x]}) ∧
  (language_of (Alt a b) = language_of a ∪ language_of b) ∧
  (language_of (Seq a b) = {(x ++ y) | x ∈ language_of a ∧ y ∈ language_of b}) ∧
  (language_of (Rep a) = {FLAT li | ∀x. MEM x li ⇒ x ∈ language_of a}) `;

(** Naive, but executable, regex matcher. **)

val split_def = Define `
  (split ([] : 'a list) = [([], [])]) ∧
  (split (c :: cs) = ([], c :: cs) :: MAP (CONS c ## I) (split cs)) `;

val add_to_head_def = Define `
  (add_to_head (c : 'a) (x :: xs) = (c :: x) :: xs)`;

val parts_def = Define `
  (parts ([] : 'a list) = [[]]) ∧
  (parts [c] = [[[c]]]) ∧
  (parts (c :: cs) = MAP (CONS [c]) (parts cs) ++ MAP (add_to_head c) (parts cs)) `;

val accept_def = Define `
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

val _ = assert_eq ``[([],[1]); ([1],[])]`` ``split [1]``;
val _ = assert_eq ``[([],[1;2]); ([1],[2]); ([1;2],[])]`` ``split [1;2]``;

val _ = assert_eq ``[[[1];[2]]; [[1;2]]]`` ``parts [1;2]``;

val _ = assert_true ``accept (Eps : 'a Reg) []``;
val _ = assert_false ``accept Eps [1]``;
val _ = assert_false ``accept (Alt (Sym 1) (Sym 2)) []``;
val _ = assert_true ``accept (Alt (Sym 1) (Sym 2)) [1]``;
val _ = assert_false ``accept (Alt (Sym 1) (Sym 2)) [3]``;
val _ = assert_false ``accept (Alt (Sym 1) (Sym 2)) [1;1]``;
val _ = assert_false ``accept (Seq (Sym 1) (Sym 2)) []``;
val _ = assert_false ``accept (Seq (Sym 1) (Sym 2)) [1]``;
val _ = assert_true ``accept (Seq (Sym 1) (Sym 2)) [1;2]``;
val _ = assert_false ``accept (Seq (Sym 1) (Sym 2)) [1;1;2]``;
val _ = assert_true ``accept (Rep (Sym 1)) []``;
val _ = assert_true ``accept (Rep (Sym 1)) [1;1;1]``;
val _ = assert_false ``accept (Rep (Sym 1)) [1;2]``;

(** Basic lemmata **)

val SPLIT_EMPTY1 = store_thm ("SPLIT_EMPTY1",
  ``∀ (a : 'a list). MEM ([], a) (split a)``,
  Cases >> SIMP_TAC list_ss [split_def]);

val SPLIT_SOUND = store_thm ("SPLIT_SOUND",
  ``∀ x y (w : 'a list). MEM (x, y) (split w) ⇒ (x ++ y = w)``,
  Induct_on `w` >| [
    SIMP_TAC list_ss [split_def],
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC list_ss [split_def, MEM_MAP, PAIR_MAP]
  ]);

val SPLIT_COMPLETE = store_thm ("SPLIT_COMPLETE",
  ``∀ a (b : 'a list). MEM (a, b) (split (a ++ b))``,
  Induct_on `a` >| [
    SIMP_TAC list_ss [split_def, SPLIT_EMPTY1],

    SIMP_TAC list_ss [split_def] >>
    `∀ (b : 'a list) (f : 'a list # 'a list -> 'a list # 'a list).
      MEM (f (a,b)) (MAP f (split (a ++ b)))`
        suffices_by (
          REPEAT STRIP_TAC >>
          `(h::a,b) = (CONS h ## I) (a,b)` by SIMP_TAC list_ss [] >>
          ASM_REWRITE_TAC[]
          ) >>
    ASM_SIMP_TAC list_ss[MEM_MAP] >>
    REPEAT STRIP_TAC >>
    Q.EXISTS_TAC `(a, b)` >>
    ASM_SIMP_TAC bool_ss []
  ]);

val PARTS_SOUND = store_thm ("PARTS_SOUND",
  ``∀ (li : 'a list) part. MEM part (parts li) ⇒ (FLAT part = li)``,
  Induct >| [
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC list_ss [parts_def],

    REPEAT STRIP_TAC >>
    Cases_on `li` >>
    FULL_SIMP_TAC list_ss [parts_def, MEM_MAP] >>

    `FLAT y = h'::t` by ASM_SIMP_TAC bool_ss[] >>
    Cases_on `y` >- FULL_SIMP_TAC list_ss [FLAT] >>

    FULL_SIMP_TAC list_ss [add_to_head_def]
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
    Q.EXISTS_TAC `[]` >>
    ASM_SIMP_TAC list_ss [FLAT, parts_def],

    FULL_SIMP_TAC bool_ss [] >>
    Cases >| [
      Q.EXISTS_TAC `part` >>
      ASM_SIMP_TAC list_ss [],

      Q.EXISTS_TAC `((h'::t) :: part)` >>
      REPEAT STRIP_TAC >| [
        WEAKEN_TAC is_forall >>
        ASM_SIMP_TAC list_ss [] >>

        (* Generalize "FLAT li" to any list *)
        `∃ rest. FLAT li = rest` by ASM_SIMP_TAC bool_ss[] >>
        FULL_SIMP_TAC bool_ss[] >>
        WEAKEN_TAC is_eq >>

        Q.ID_SPEC_TAC `h'` >>
        Induct_on `t` >| [
          ASM_SIMP_TAC list_ss [] >>
          Cases_on `rest` >>
          FULL_SIMP_TAC list_ss [parts_def, add_to_head_def] >>
          Cases_on `t` >>
          FULL_SIMP_TAC list_ss [parts_def, add_to_head_def, MEM_MAP] >>
          METIS_TAC[parts_def, add_to_head_def],

          FULL_SIMP_TAC list_ss [parts_def, add_to_head_def] >>
          METIS_TAC[parts_def, add_to_head_def, MEM_MAP]
        ],

        FULL_SIMP_TAC list_ss []
      ]
    ]
  ]);

val ACCEPT_SEQ_CONCAT = store_thm ("ACCEPT_SEQ_CONCAT",
  ``∀ p q u (v : 'a list).
    accept p u ∧ accept q v ⇒ accept (Seq p q) (u ++ v)``,
  REPEAT STRIP_TAC >>
  SIMP_TAC list_ss [accept_def, EXISTS_MEM] >>
  Q.EXISTS_TAC `(u, v)` >>
  ASM_SIMP_TAC std_ss [SPLIT_COMPLETE]);

val ACCEPT_REP_NIL = store_thm ("ACCEPT_REP_NIL",
  ``∀ (p : 'a Reg). accept (Rep p) []``,
  SIMP_TAC list_ss [accept_def, parts_def]);

(** Equivalence with language **)

val set_ss = std_ss ++ SET_SPEC_ss;

val ACCEPT_IN_LANG = prove (
  ``∀ (r : 'a Reg) w. accept r w ⇒  w ∈ (language_of r)``,
  Induct >> REPEAT STRIP_TAC >>
  FULL_SIMP_TAC set_ss [language_of_def, accept_def, IN_SING, IN_UNION, NULL] >| [
    Cases_on `w` >> FULL_SIMP_TAC list_ss [],

    FULL_SIMP_TAC (std_ss ++ gen_beta_ss) [EXISTS_MEM] >>
    Q.EXISTS_TAC `FST e` >>
    Q.EXISTS_TAC `SND e` >>
    ASM_SIMP_TAC std_ss [SPLIT_SOUND],

    FULL_SIMP_TAC std_ss [EXISTS_MEM, EVERY_MEM] >>
    Q.EXISTS_TAC `e` >>
    FULL_SIMP_TAC std_ss [PARTS_SOUND]
  ]);

val LANG_IN_ACCEPT = prove (
  ``∀ (r : 'a Reg) w. w ∈ (language_of r) ⇒ accept r w``,
  Induct >> REPEAT STRIP_TAC >>
  FULL_SIMP_TAC set_ss [language_of_def, accept_def, IN_SING, IN_UNION, NULL] >| [
    METIS_TAC [accept_def, ACCEPT_SEQ_CONCAT],

    `∃ part. MEM part (parts (FLAT li)) ∧ ∀ x. (MEM x part ⇒ MEM x li)`
      by REWRITE_TAC [PARTS_IN_FLAT] >>
    SIMP_TAC list_ss [EXISTS_MEM] >>
    Q.EXISTS_TAC `part` >>
    ASM_SIMP_TAC std_ss [EVERY_MEM]
  ]);

val ACCEPT_CORRECT = store_thm ("ACCEPT_CORRECT",
  ``∀ (r : 'a Reg) w. accept r w ⇔ w ∈ (language_of r)``,
  REPEAT STRIP_TAC >>
  EQ_TAC >>
  REWRITE_TAC [ACCEPT_IN_LANG, LANG_IN_ACCEPT]);

(** Definition of a marked regex, on which the optimized-but-uncached regex
 * matcher operates **)

val _ = Datatype `
  MReg = MEps |
    MSym bool 'a |
    MAlt MReg MReg |
    MSeq MReg MReg |
    MRep MReg |
    MInit bool MReg`;

(** Optimized-but-uncached regex matcher. **)

val empty_def = Define `
  (empty MEps = T) ∧
  (empty (MSym _ (_ : 'a)) = F) ∧
  (empty (MAlt p q) = empty p ∨ empty q) ∧
  (empty (MSeq p q) = empty p ∧ empty q) ∧
  (empty (MRep r) = T) ∧
  (empty (MInit _ r) = empty r)`;

val final_def = Define `
  (final MEps = F) ∧
  (final (MSym b (_ : 'a)) = b) ∧
  (final (MAlt p q) = final p ∨ final q) ∧
  (final (MSeq p q) = (final p ∧ empty q) ∨ final q) ∧
  (final (MRep r) = final r) ∧
  (final (MInit b r) = (b ∧ empty r) ∨ final r)`;

val shift_def = Define `
  (shift _ MEps _ = MEps) ∧
  (shift m (MSym _ x) c = MSym (m ∧ (x = c)) x) ∧
  (shift m (MAlt p q) c = MAlt (shift m p c) (shift m q c)) ∧
  (shift m (MSeq p q) c = MSeq (shift m p c) (shift ((m ∧ empty p) ∨ final p) q c)) ∧
  (shift m (MRep r) c = MRep (shift (m ∨ final r) r c)) ∧
  (shift m (MInit b r) c = MInit F (shift (m ∨ b) r c))`;

val acceptM_def = Define `
  acceptM mr (s : 'a list) = final (FOLDL (shift F) (MInit T mr) s)`;

val mark_reg_def = Define `
  (mark_reg Eps = MEps) ∧
  (mark_reg (Sym (c : 'a)) = MSym F c) ∧
  (mark_reg (Alt p q) = MAlt (mark_reg p) (mark_reg q)) ∧
  (mark_reg (Seq p q) = MSeq (mark_reg p) (mark_reg q)) ∧
  (mark_reg (Rep r) = MRep (mark_reg r)) `;

val is_marked_reg_def = Define `
  (is_marked_reg Eps MEps = T) ∧
  (is_marked_reg (Sym (c : 'a)) (MSym _ mc) = (c = mc)) ∧
  (is_marked_reg (Alt p q) (MAlt mp mq) = is_marked_reg p mp ∧ is_marked_reg q mq) ∧
  (is_marked_reg (Seq p q) (MSeq mp mq) = is_marked_reg p mp ∧ is_marked_reg q mq) ∧
  (is_marked_reg (Rep r) (MRep mr) = is_marked_reg r mr) ∧
  (is_marked_reg _ _ = F) `;

val mark_le_def = Define `
  (mark_le MEps MEps = T) ∧
  (mark_le (MSym ma (c : 'a)) (MSym mb d) = ((c = d) ∧ (ma ⇒ mb))) ∧
  (mark_le (MAlt p q) (MAlt mp mq) = mark_le p mp ∧ mark_le q mq) ∧
  (mark_le (MSeq p q) (MSeq mp mq) = mark_le p mp ∧ mark_le q mq) ∧
  (mark_le (MRep r) (MRep mr) = mark_le r mr) ∧
  (mark_le (MInit b1 r) (MInit b2 mr) = (b1 ⇒ b2) ∧ mark_le r mr) ∧
  (mark_le _ _ = F) `;

val mark_union_def = Define `
  (mark_union MEps MEps = MEps) ∧
  (mark_union (MSym ma (c : 'a)) (MSym mb _) = MSym (ma ∨ mb) c) ∧
  (mark_union (MAlt p q) (MAlt mp mq) = MAlt (mark_union p mp) (mark_union q mq)) ∧
  (mark_union (MSeq p q) (MSeq mp mq) = MSeq (mark_union p mp) (mark_union q mq)) ∧
  (mark_union (MRep ma) (MRep mb) = MRep (mark_union ma mb)) ∧
  (mark_union (MInit b1 ma) (MInit b2 mb) = MInit (b1 ∨ b2) (mark_union ma mb))`;

(** Some tests **)

val accept2_def = Define `accept2 r l = acceptM (mark_reg r) l`;

val _ = assert_true ``empty (MAlt MEps (MEps : 'a MReg))``;
val _ = assert_true ``empty (MAlt MEps (MSym T 2))``;
val _ = assert_false ``empty (MAlt (MSym T 1) (MSym T 2))``;

val _ = assert_false ``final (MAlt MEps (MEps : 'a MReg))``;
val _ = assert_true ``final (MAlt MEps (MSym T 2))``;
val _ = assert_true ``final (MSeq MEps (MSym T 2))``;
val _ = assert_true ``final (MSeq (MSym T 2) MEps)``;
val _ = assert_true ``final (MSeq (MSym T 2) (MSym T 3))``;
val _ = assert_false ``final (MSeq (MSym T 2) (MSym F 3))``;

val _ = assert_true ``accept2 (Eps : 'a Reg) []``;
val _ = assert_false ``accept2 Eps [1]``;
val _ = assert_false ``accept2 (Alt (Sym 1) (Sym 2)) []``;
val _ = assert_true ``accept2 (Alt (Sym 1) (Sym 2)) [1]``;
val _ = assert_false ``accept2 (Alt (Sym 1) (Sym 2)) [3]``;
val _ = assert_false ``accept2 (Alt (Sym 1) (Sym 2)) [1;1]``;
val _ = assert_false ``accept2 (Seq (Sym 1) (Sym 2)) []``;
val _ = assert_false ``accept2 (Seq (Sym 1) (Sym 2)) [1]``;
val _ = assert_true ``accept2 (Seq (Sym 1) (Sym 2)) [1;2]``;
val _ = assert_false ``accept2 (Seq (Sym 1) (Sym 2)) [1;1;2]``;
val _ = assert_true ``accept2 (Rep (Sym 1)) []``;
val _ = assert_true ``accept2 (Rep (Sym 1)) [1;1;1]``;
val _ = assert_false ``accept2 (Rep (Sym 1)) [1;2]``;

(** Basic lemmata **)

val MARK_IS_MARKED = store_thm ("MARK_IS_MARKED",
  ``∀ (r : 'a Reg). is_marked_reg r (mark_reg r)``,
  Induct >> ASM_REWRITE_TAC[mark_reg_def, is_marked_reg_def]);

val SHIFT_IS_MARKED = store_thm ("SHIFT_IS_MARKED",
  ``∀ (r : 'a Reg) mr m c.
    is_marked_reg r mr ⇒ is_marked_reg r (shift m mr c)``,
  Induct >> Cases_on `mr` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC bool_ss [shift_def, is_marked_reg_def]);

val FOLDL_SHIFT_IS_MARKED = prove (
  ``∀ (r : 'a Reg) mr m w.
    is_marked_reg r mr ⇒ is_marked_reg r (FOLDL (shift F) mr w)``,
  NTAC 3 STRIP_TAC >>
  INDUCT_THEN SNOC_INDUCT ASSUME_TAC >>
  FULL_SIMP_TAC bool_ss [FOLDL, FOLDL_SNOC, SHIFT_IS_MARKED]);

val EMPTY_SOUND = store_thm ("EMPTY_SOUND",
  ``∀ r (mr : 'a MReg). empty mr ∧ is_marked_reg r mr ⇒ [] ∈ language_of r``,
  Induct >> Cases_on `mr` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (list_ss ++ SET_SPEC_ss ++ QI_ss)
    [empty_def, is_marked_reg_def, language_of_def, IN_SING] >>
  Q.EXISTS_TAC `[]` >>
  SIMP_TAC list_ss []);

val EMPTY_COMPLETE = store_thm ("EMPTY_COMPLETE",
  ``∀ r (mr : 'a MReg). [] ∈ language_of r ∧ is_marked_reg r mr ⇒ empty mr``,
  Induct >> Cases_on `mr` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (list_ss ++ SET_SPEC_ss) [empty_def, is_marked_reg_def, language_of_def, IN_SING]);

val MARK_LE_REFL = store_thm ("MARK_LE_REFL",
  ``∀ (r : 'a MReg). mark_le r r``,
  Induct >> ASM_REWRITE_TAC[mark_le_def]);

val MARK_LE_TRANS = store_thm ("MARK_LE_TRANS",
  ``∀ r s (t : 'a MReg). mark_le r s ∧ mark_le s t ⇒ mark_le r t``,
  Induct >> Cases_on `s` >> Cases_on `t` >>
  ASM_REWRITE_TAC [mark_le_def] >> METIS_TAC []);

val EMPTY_LE = store_thm ("EMPTY_LE",
  ``∀ r (s : 'a MReg). mark_le r s ⇒ (empty r = empty s)``,
  Induct >> Cases_on `s` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC bool_ss[mark_le_def, empty_def] >>
  METIS_TAC[]);

val FINAL_LE = store_thm ("FINAL_LE",
  ``∀ r (s : 'a MReg). mark_le r s ∧ final r ⇒ final s``,
  Induct >> Cases_on `s` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC bool_ss[mark_le_def, final_def] >>
  METIS_TAC [EMPTY_LE]);

val SHIFT_LE = store_thm ("SHIFT_LE",
  ``∀ r s (c : 'a) b1 b2.
      (b1 ⇒ b2) ⇒ (mark_le r s) ⇒ mark_le (shift b1 r c) (shift b2 s c)``,
  Induct >> Cases_on `s` >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC bool_ss[shift_def, mark_le_def] >>
    `empty r = empty M` by (ASM_SIMP_TAC bool_ss [EMPTY_LE]) >>
    `(final r ⇒ final M)` by (METIS_TAC [FINAL_LE]) >>
    Cases_on `empty r` >> Cases_on `final r` >>
    Cases_on `empty M` >> Cases_on `final M` >>
    FULL_SIMP_TAC bool_ss [] >>
    Cases_on `b1` >> Cases_on `b2` >>
    FULL_SIMP_TAC bool_ss []);

val MARK_REG_LE = store_thm ("MARK_REG_LE",
  ``∀ r (mr : 'a MReg). is_marked_reg r mr ⇒ mark_le (mark_reg r) mr``,
  Induct >> Cases_on `mr` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def, mark_reg_def, mark_le_def]);

val IS_MARKED_REG_LE = store_thm ("IS_MARKED_REG_LE",
  ``∀ r mr (ms : 'a MReg). is_marked_reg r mr ∧ mark_le mr ms ⇒ is_marked_reg r ms``,
  Induct >> Cases_on `mr` >> Cases_on `ms` >>
  ASM_SIMP_TAC bool_ss [is_marked_reg_def, mark_le_def] >>
  METIS_TAC []);

val MARK_REG_NOT_FINAL = store_thm ("MARK_REG_NOT_FINAL",
  ``∀ (r : 'a Reg). ¬final (mark_reg r)``,
  Induct >> FULL_SIMP_TAC bool_ss [mark_reg_def, final_def]);

val SHIFT_MARK_REG_F = store_thm ("SHIFT_MARK_REG_F",
  ``∀ (r : 'a Reg) c. shift F (mark_reg r) c = mark_reg r``,
  Induct >> FULL_SIMP_TAC bool_ss [mark_reg_def, shift_def, MARK_REG_NOT_FINAL]);

val FOLDL_MINIT_F = store_thm ("FOLDL_MINIT_F",
  ``∀ w (mr : 'a MReg).
    FOLDL (shift F) (MInit F mr) w = MInit F (FOLDL (shift F) mr w)``,
  INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
    SIMP_TAC list_ss [],
    ASM_SIMP_TAC list_ss [FOLDL_SNOC, shift_def]
  ]);

val MARK_UNION_MARKED = store_thm ("MARK_UNION_MARKED",
  ``∀ (r : 'a Reg) ma mb.
    is_marked_reg r ma ∧ is_marked_reg r mb ⇒ is_marked_reg r (mark_union ma mb)``,
  Induct >> Cases_on `ma` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def] >>
  Cases_on `mb` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def, mark_union_def]);

val IS_MARKED_EMPTY = store_thm ("IS_MARKED_EMPTY",
  ``∀ (r : 'a Reg) ma mb.
    is_marked_reg r ma ∧ is_marked_reg r mb ⇒ (empty ma = empty mb)``,
  Induct >> Cases_on `ma` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def] >>
  Cases_on `mb` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def, empty_def] >>
  METIS_TAC[]);

val MARK_UNION_FINAL = store_thm ("MARK_UNION_FINAL",
  ``∀ (r : 'a Reg) ma mb.
    is_marked_reg r ma ∧ is_marked_reg r mb ⇒
    (final (mark_union ma mb) = final ma ∨ final mb)``,
  Induct >> Cases_on `ma` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def] >>
  Cases_on `mb` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def] >>
  FULL_SIMP_TAC bool_ss [mark_union_def, final_def] >>
  METIS_TAC[IS_MARKED_EMPTY, MARK_UNION_MARKED]);

val MARK_UNION_EMPTY = store_thm ("MARK_UNION_EMPTY",
  ``∀ (r : 'a Reg) ma mb.
    is_marked_reg r ma ∧ is_marked_reg r mb ⇒
    (empty (mark_union ma mb) = empty ma)``,
  Induct >> Cases_on `ma` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def] >>
  Cases_on `mb` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def] >>
  FULL_SIMP_TAC bool_ss [mark_union_def, empty_def]);

val MARK_UNION_ID = store_thm ("MARK_UNION_ID",
  ``∀ (r : 'a Reg) ma.
    is_marked_reg r ma ⇒ (mark_union (mark_reg r) ma = ma)``,
  Induct >> Cases_on `ma` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def, mark_reg_def, mark_union_def]);

val MARK_UNION_SHIFT = store_thm ("MARK_UNION_SHIFT",
  ``∀ (r : 'a Reg) ma mb b1 b2 c.
    is_marked_reg r ma ∧ is_marked_reg r mb ⇒
    (mark_union (shift b1 ma c) (shift b2 mb c) = shift (b1 ∨ b2) (mark_union ma mb) c)``,
  Induct >> Cases_on `ma` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def] >>
  Cases_on `mb` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg_def] >>
  REPEAT STRIP_TAC >| [
    FULL_SIMP_TAC bool_ss [mark_union_def, shift_def],

    FULL_SIMP_TAC bool_ss [mark_union_def, shift_def] >>
    Cases_on `b1` >> Cases_on `b2` >> Cases_on `a' = c` >> SIMP_TAC bool_ss [],

    FULL_SIMP_TAC bool_ss [mark_union_def, shift_def],

    RW_TAC bool_ss [mark_union_def, shift_def] >>
    ASM_SIMP_TAC (bool_ss ++ QI_ss ++ DNF_ss)
      [MARK_UNION_EMPTY, MARK_UNION_FINAL] >>
    `empty M' = empty M` by METIS_TAC[IS_MARKED_EMPTY] >>
    ASM_SIMP_TAC (bool_ss ++ DNF_ss) [] >>
    `((b1 ∧ empty M ∨ final M) ∨ b2 ∧ empty M ∨ final M') =
    ((b1 ∧ empty M ∨ b2 ∧ empty M) ∨ final M ∨ final M')`
      suffices_by ASM_SIMP_TAC bool_ss [] >>
    METIS_TAC [],

    RW_TAC bool_ss [mark_union_def, shift_def] >>
    ASM_SIMP_TAC (bool_ss ++ QI_ss) [MARK_UNION_FINAL] >>
    `((b1 ∨ final M) ∨ b2 ∨ final M') = ((b1 ∨ b2) ∨ final M ∨ final M')`
      suffices_by ASM_SIMP_TAC bool_ss [] >>
    METIS_TAC []
  ]);

(** Equivalence with language **)

val ACCEPTM_ALT = store_thm ("ACCEPTM_ALT",
  ``∀ p q (li : 'a list). (acceptM p li ∨ acceptM q li) ⇔ acceptM (MAlt p q) li``,
  NTAC 3 STRIP_TAC >>
  FULL_SIMP_TAC bool_ss [acceptM_def] >>
  `∃ mp mq b.
    (FOLDL (shift F) (MInit T p) li = MInit b mp) ∧
    (FOLDL (shift F) (MInit T q) li = MInit b mq) ∧
    (FOLDL (shift F) (MInit T (MAlt p q)) li = MInit b (MAlt mp mq))` by (
    Q.ID_SPEC_TAC `li` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      METIS_TAC [MARK_LE_REFL],
      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [shift_def, FOLDL_SNOC] >>
      RW_TAC (bool_ss ++ QI_ss) [SHIFT_LE]
    ]) >>
  METIS_TAC [final_def, empty_def]);

val ACCEPTM_REP_APPEND = prove (
  ``∀ r x (y : 'a list).
    acceptM (MRep (mark_reg r)) x ∧ acceptM (mark_reg r) y ⇒
      acceptM (MRep (mark_reg r)) (x ++ y)``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC list_ss [acceptM_def, FOLDL_APPEND] >>

  `∃ mr b. mark_le (mark_reg r) mr ∧
    (FOLDL (shift F) (MInit T (MRep (mark_reg r))) x = MInit b (MRep mr))` by (
    Q.ID_SPEC_TAC `x` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      METIS_TAC [MARK_LE_REFL],

      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [shift_def, FOLDL_SNOC] >>
      METIS_TAC [MARK_REG_LE, SHIFT_IS_MARKED, MARK_IS_MARKED, IS_MARKED_REG_LE]
    ]) >>

  FULL_SIMP_TAC list_ss [] >>
  WEAKEN_TAC is_eq >>

  `∃ mr2 b2 mr3 b3. mark_le mr3 mr2 ∧ (b3 ⇒ b2 ∨ final mr2) ∧
    (FOLDL (shift F) (MInit T (mark_reg r)) y = (MInit b3 mr3)) ∧
    (FOLDL (shift F) (MInit b (MRep mr)) y = MInit b2 (MRep mr2))` by (
    Q.ID_SPEC_TAC `y` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      METIS_TAC [final_def],

      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [shift_def, FOLDL_SNOC] >>
      REPEAT (WEAKEN_TAC is_eq) >>
      RW_TAC (bool_ss ++ QI_ss) [] >>
      ASM_SIMP_TAC bool_ss [SHIFT_LE]
      (* It's odd that METIS isn't able to deal with this *)
    ]) >>

  METIS_TAC [final_def, empty_def, FINAL_LE]);

val ACCEPTM_REP = prove (
  ``∀ r (li : 'a list list).
    (∀ x. MEM x li ⇒ acceptM (mark_reg r) x) ⇒
      acceptM (MRep (mark_reg r)) (FLAT li)``,
  STRIP_TAC >>
  INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
    FULL_SIMP_TAC list_ss [acceptM_def, empty_def, final_def],
    FULL_SIMP_TAC list_ss [FLAT_SNOC, ACCEPTM_REP_APPEND]
  ]);

val ACCEPTM_SEQ = prove (
  ``∀ ra rb x (y : 'a list).
    acceptM (mark_reg ra) x ∧ acceptM (mark_reg rb) y ⇒
      acceptM (MSeq (mark_reg ra) (mark_reg rb)) (x ++ y)``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC list_ss [acceptM_def, FOLDL_APPEND] >>

  `∃ ma mb b. mark_le (mark_reg ra) ma ∧ mark_le (mark_reg rb) mb ∧
    (FOLDL (shift F) (MInit T (mark_reg ra)) x = MInit b ma) ∧
    (FOLDL (shift F) (MInit T (MSeq (mark_reg ra) (mark_reg rb))) x = MInit b (MSeq ma mb))` by (
    Q.ID_SPEC_TAC `x` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      METIS_TAC [MARK_LE_REFL],

      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [FOLDL_SNOC, shift_def] >>
      REPEAT (WEAKEN_TAC is_eq) >>

      Q.EXISTS_TAC `shift b ma x''` >>
      Q.EXISTS_TAC `shift (b ∧ empty ma ∨ final ma) mb x''` >>
      Q.EXISTS_TAC `F` >>
      METIS_TAC [MARK_REG_LE, SHIFT_IS_MARKED, MARK_IS_MARKED, IS_MARKED_REG_LE]
    ]) >>

  FULL_SIMP_TAC list_ss [] >>
  REPEAT (WEAKEN_TAC is_eq) >>

  `∃ rb2 b2 ma2 mb2 b3. mark_le rb2 mb2 ∧ (b2 ⇒ b3 ∧ empty ma2 ∨ final ma2) ∧
    (FOLDL (shift F) (MInit T (mark_reg rb)) y = MInit b2 rb2) ∧
    (FOLDL (shift F) (MInit b (MSeq ma mb)) y = MInit b3 (MSeq ma2 mb2))` by (
    Q.ID_SPEC_TAC `y` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      RW_TAC (bool_ss ++ QI_ss) [] >>
      FULL_SIMP_TAC bool_ss [final_def],

      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [FOLDL_SNOC, shift_def] >>
      REPEAT (WEAKEN_TAC is_eq) >>

      RW_TAC (bool_ss ++ QI_ss) [SHIFT_LE]
    ]) >>

  METIS_TAC [final_def, empty_def, FINAL_LE, EMPTY_LE]);

val LANG_IN_ACCEPTM = prove (
  ``∀ (r : 'a Reg) w. w ∈ (language_of r) ⇒ acceptM (mark_reg r) w``,
  Induct >>
  FULL_SIMP_TAC bool_ss [mark_reg_def, is_marked_reg_def, language_of_def] >>
  REPEAT STRIP_TAC >| [
    FULL_SIMP_TAC list_ss [IN_SING, acceptM_def, empty_def, final_def],
    FULL_SIMP_TAC list_ss [IN_SING, acceptM_def, empty_def, final_def, shift_def],
    METIS_TAC [IN_UNION, ACCEPTM_ALT],
    FULL_SIMP_TAC set_ss [ACCEPTM_SEQ],
    FULL_SIMP_TAC set_ss [ACCEPTM_REP]
  ]);

val ACCEPTM_SEQ_SOUND = prove (
  ``∀ w b mr (r : 'a Reg).
  final (FOLDL (shift F) (MInit b (MSeq mr (mark_reg r))) w) ⇒
    ∃ x y. (w = x ++ y) ∧
      final (FOLDL (shift F) (MInit b mr) x) ∧
      acceptM (mark_reg r) y``,
  Induct >| [
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (list_ss ++ QI_ss) [acceptM_def, final_def, empty_def, MARK_REG_NOT_FINAL],

    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC list_ss [FOLDL, shift_def] >>

    Q.ABBREV_TAC `acleft = b ∧ empty mr ∨ final mr` >>
    Q.ABBREV_TAC `right = FOLDL (shift F) (shift T (mark_reg r) h) w` >>

    Cases_on `acleft ∧ final right` >| [
      Q.EXISTS_TAC `[]` >>
      Q.EXISTS_TAC `h :: w` >>
      ASM_SIMP_TAC list_ss [final_def, acceptM_def, shift_def, FOLDL, FOLDL_MINIT_F],

      `final (FOLDL (shift F) (MInit F (MSeq (shift b mr h) (mark_reg r))) w)` by (
        Cases_on `acleft` >| [
          FULL_SIMP_TAC bool_ss [] >>
          Q.UNABBREV_TAC `right` >>
          Q.PAT_X_ASSUM `Abbrev _` kall_tac >>

          `∃ ma mb mb'.
          (FOLDL (shift F)
            (MInit F (MSeq (shift b mr h) (shift T (mark_reg r) h))) w =
          MInit F (MSeq ma mb)) ∧
          (FOLDL (shift F)
            (MInit F (MSeq (shift b mr h) (shift F (mark_reg r) h))) w =
          MInit F (MSeq ma mb')) ∧
          (mb = mark_union mb' (FOLDL (shift F) (shift T (mark_reg r) h) w)) ∧
          is_marked_reg r mb' ` by (
            REPEAT (WEAKEN_TAC (K true)) >>
            Q.ID_SPEC_TAC `w` >>
            INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
              SIMP_TAC list_ss [FOLDL] >>
              Q.EXISTS_TAC `shift b mr h` >>
              Q.EXISTS_TAC `shift F (mark_reg r) h` >>
              SIMP_TAC bool_ss [SHIFT_MARK_REG_F, MARK_UNION_ID, MARK_IS_MARKED,
                               SHIFT_IS_MARKED],

              STRIP_TAC >>
              FULL_SIMP_TAC list_ss [FOLDL, FOLDL_SNOC, shift_def] >>
              Q.EXISTS_TAC `shift F ma x` >>
              Q.EXISTS_TAC `shift (final ma) mb' x` >>
              FULL_SIMP_TAC bool_ss [SHIFT_IS_MARKED] >>
              RW_TAC bool_ss [] >>

              Q.ABBREV_TAC `mb2 = FOLDL (shift F) (shift T (mark_reg r) h) w` >>
              `is_marked_reg r mb2`
                by FULL_SIMP_TAC bool_ss [MARK_IS_MARKED, SHIFT_IS_MARKED,
                                          FOLDL_SHIFT_IS_MARKED, Abbr`mb2`] >>

              FULL_SIMP_TAC (bool_ss ++ QI_ss) [MARK_UNION_SHIFT]
            ]
          ) >>

          FULL_SIMP_TAC bool_ss [SHIFT_MARK_REG_F] >>
          `is_marked_reg r (FOLDL (shift F) (shift T (mark_reg r) h) w)`
            by FULL_SIMP_TAC bool_ss [FOLDL_SHIFT_IS_MARKED, SHIFT_IS_MARKED,
                                                   MARK_IS_MARKED] >>

          FULL_SIMP_TAC bool_ss [final_def] >| [
            `empty mb'` suffices_by SIMP_TAC bool_ss [] >>
            METIS_TAC [MARK_UNION_EMPTY, FOLDL_SHIFT_IS_MARKED, SHIFT_IS_MARKED],

            `final mb'` suffices_by SIMP_TAC bool_ss [] >>
            METIS_TAC [MARK_UNION_FINAL]
          ],

          FULL_SIMP_TAC bool_ss [SHIFT_MARK_REG_F]
        ]) >>

      `∃ x y. (w = x ++ y) ∧ final (FOLDL (shift F) (MInit F (shift b mr h)) x) ∧
          acceptM (mark_reg r) y`
        by ASM_SIMP_TAC bool_ss [] >>
      Q.EXISTS_TAC `h :: x` >>
      Q.EXISTS_TAC `y` >>
      FULL_SIMP_TAC list_ss [shift_def]
    ]
  ]);

val ACCEPTM_REP_SOUND = prove (
  ``∀ w mr (r : 'a Reg).
  is_marked_reg r mr ⇒
  final (FOLDL (shift F) (MInit F (MRep mr)) w) ⇒
    ∃ x y. (w = x ++ y) ∧
      final (FOLDL (shift F) (MInit F mr) x) ∧
      acceptM (MRep (mark_reg r)) y``,
  cheat);

val ACCEPTM_IN_LANG = prove (
  ``∀ (r : 'a Reg) w. acceptM (mark_reg r) w ⇒ w ∈ (language_of r)``,
  Induct >>
  FULL_SIMP_TAC bool_ss [language_of_def, IN_SING] >>
  REPEAT STRIP_TAC >| [
    (* MEps *)
    Cases_on `w` >- SIMP_TAC bool_ss [] >>
    FULL_SIMP_TAC bool_ss [acceptM_def, shift_def, mark_reg_def, FOLDL] >>
    `FOLDL (shift F) (MInit F MEps) t = MInit F MEps` by (
      Induct_on `t` >| [
        FULL_SIMP_TAC list_ss [],
        FULL_SIMP_TAC list_ss [shift_def]
      ]) >>
    FULL_SIMP_TAC bool_ss [final_def],

    (* MSym *)
    Cases_on `w` >-
      FULL_SIMP_TAC list_ss [acceptM_def, mark_reg_def, final_def, empty_def, FOLDL] >>
    Cases_on `t` >-
      FULL_SIMP_TAC list_ss [acceptM_def, mark_reg_def, final_def, empty_def,
      shift_def, FOLDL] >>
    Q.RENAME1_TAC `h1 :: h2 :: t` >>
    FULL_SIMP_TAC bool_ss [acceptM_def, shift_def, mark_reg_def, FOLDL] >>
    `FOLDL (shift F) (MInit F (MSym F a)) t = MInit F (MSym F a)` by (
      Induct_on `t` >| [
        FULL_SIMP_TAC list_ss [],
        FULL_SIMP_TAC list_ss [shift_def]
      ]) >>
    FULL_SIMP_TAC bool_ss [final_def],

    (* MAlt *)
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC set_ss [mark_reg_def, IN_UNION] >>
    METIS_TAC [ACCEPTM_ALT],

    (* MSeq *)
    FULL_SIMP_TAC set_ss [acceptM_def] >>

    `final (FOLDL (shift F) (MInit T (MSeq (mark_reg r) (mark_reg r'))) w)` by
      METIS_TAC [acceptM_def, mark_reg_def] >>

    `∃ x y. (w = x ++ y) ∧
      final (FOLDL (shift F) (MInit T (mark_reg r)) x) ∧
      acceptM (mark_reg r') y` by
      METIS_TAC [ACCEPTM_SEQ_SOUND] >>

    Q.EXISTS_TAC `x` >>
    Q.EXISTS_TAC `y` >>
    FULL_SIMP_TAC set_ss [acceptM_def],

    (* MRep *)
    FULL_SIMP_TAC set_ss [mark_reg_def] >>
    Q.UNDISCH_TAC `acceptM (MRep (mark_reg r)) w` >>
    measureInduct_on `LENGTH w` >>
    Cases_on `w` >| [
      STRIP_TAC >>
      Q.EXISTS_TAC `[]` >>
      FULL_SIMP_TAC list_ss [],

      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC list_ss [acceptM_def, shift_def] >>
      `is_marked_reg r (shift T (mark_reg r) h)`
        by METIS_TAC [SHIFT_IS_MARKED, MARK_IS_MARKED] >>
      `∃ x y. (t = x ++ y) ∧
              final (FOLDL (shift F) (MInit F (shift T (mark_reg r) h)) x) ∧
              acceptM (MRep (mark_reg r)) y`
        by METIS_TAC [ACCEPTM_REP_SOUND] >>
      FULL_SIMP_TAC list_ss [acceptM_def] >>
      `LENGTH y < SUC (LENGTH x + LENGTH y)` by DECIDE_TAC >>
      `∃li. (y = FLAT li) ∧ ∀x. MEM x li ⇒ x ∈ language_of r`
        by METIS_TAC [] >>
      Q.EXISTS_TAC `(h :: x) :: li` >>
      ASM_SIMP_TAC list_ss [] >>
      `(h::x) ∈ language_of r`
        suffices_by METIS_TAC [] >>
      `final (FOLDL (shift F) (MInit T (mark_reg r)) (h::x))`
        suffices_by METIS_TAC [] >>
      FULL_SIMP_TAC list_ss [shift_def]
    ]
  ]);

val ACCEPTM_CORRECT = store_thm ("ACCEPTM_CORRECT",
  ``∀ (r : 'a Reg) w. acceptM (mark_reg r) w ⇔ w ∈ (language_of r)``,
  REPEAT STRIP_TAC >>
  EQ_TAC >>
  REWRITE_TAC [ACCEPTM_IN_LANG, LANG_IN_ACCEPTM]);

val _ = export_theory();
