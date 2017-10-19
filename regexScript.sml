open HolKernel Parse boolLib bossLib;

val _ = new_theory "regex";

open listTheory rich_listTheory pairTheory pairSimps pred_setTheory patternMatchesSyntax;

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

val empty = Define `
  (empty MEps = T) ∧
  (empty (MSym _ (_ : 'a)) = F) ∧
  (empty (MAlt p q) = empty p ∨ empty q) ∧
  (empty (MSeq p q) = empty p ∧ empty q) ∧
  (empty (MRep r) = T) ∧
  (empty (MInit _ r) = empty r)`;

val final = Define `
  (final MEps = F) ∧
  (final (MSym b (_ : 'a)) = b) ∧
  (final (MAlt p q) = final p ∨ final q) ∧
  (final (MSeq p q) = (final p ∧ empty q) ∨ final q) ∧
  (final (MRep r) = final r) ∧
  (final (MInit b r) = (b ∧ empty r) ∨ final r)`;

val shift = Define `
  (shift _ MEps _ = MEps) ∧
  (shift m (MSym _ x) c = MSym (m ∧ (x = c)) x) ∧
  (shift m (MAlt p q) c = MAlt (shift m p c) (shift m q c)) ∧
  (shift m (MSeq p q) c = MSeq (shift m p c) (shift ((m ∧ empty p) ∨ final p) q c)) ∧
  (shift m (MRep r) c = MRep (shift (m ∨ final r) r c)) ∧
  (shift m (MInit b r) c = MInit F (shift (m ∨ b) r c))`;

val acceptM = Define `
  acceptM mr (s : 'a list) = final (FOLDL (shift F) (MInit T mr) s)`;

val mark_reg = Define `
  (mark_reg Eps = MEps) ∧
  (mark_reg (Sym (c : 'a)) = MSym F c) ∧
  (mark_reg (Alt p q) = MAlt (mark_reg p) (mark_reg q)) ∧
  (mark_reg (Seq p q) = MSeq (mark_reg p) (mark_reg q)) ∧
  (mark_reg (Rep r) = MRep (mark_reg r)) `;

val is_marked_reg = Define `
  (is_marked_reg Eps MEps = T) ∧
  (is_marked_reg (Sym (c : 'a)) (MSym _ mc) = (c = mc)) ∧
  (is_marked_reg (Alt p q) (MAlt mp mq) = is_marked_reg p mp ∧ is_marked_reg q mq) ∧
  (is_marked_reg (Seq p q) (MSeq mp mq) = is_marked_reg p mp ∧ is_marked_reg q mq) ∧
  (is_marked_reg (Rep r) (MRep mr) = is_marked_reg r mr) ∧
  (is_marked_reg _ _ = F) `;

val mark_le = Define `
  (mark_le MEps MEps = T) ∧
  (mark_le (MSym ma (c : 'a)) (MSym mb d) = ((c = d) ∧ (ma ⇒ mb))) ∧
  (mark_le (MAlt p q) (MAlt mp mq) = mark_le p mp ∧ mark_le q mq) ∧
  (mark_le (MSeq p q) (MSeq mp mq) = mark_le p mp ∧ mark_le q mq) ∧
  (mark_le (MRep r) (MRep mr) = mark_le r mr) ∧
  (mark_le (MInit b1 r) (MInit b2 mr) = (b1 ⇒ b2) ∧ mark_le r mr) ∧
  (mark_le _ _ = F) `;

(** Some tests **)

val _ = Define `accept2 r l = acceptM (mark_reg r) l`;

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
  Induct >> ASM_REWRITE_TAC[mark_reg, is_marked_reg]);

val SHIFT_IS_MARKED = store_thm ("SHIFT_IS_MARKED",
  ``∀ (r : 'a Reg) mr m c.
    is_marked_reg r mr ⇒ is_marked_reg r (shift m mr c)``,
  Induct >> Cases_on `mr` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC bool_ss [shift, is_marked_reg]);

val EMPTY_SOUND = store_thm ("EMPTY_SOUND",
  ``∀ r (mr : 'a MReg). empty mr ∧ is_marked_reg r mr ⇒ [] ∈ language_of r``,
  Induct >> Cases_on `mr` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (list_ss ++ SET_SPEC_ss ++ QI_ss)
    [empty, is_marked_reg, language_of, IN_SING] >>
  EXISTS_TAC ``[] : 'a list list`` >>
  SIMP_TAC list_ss []);

val EMPTY_COMPLETE = store_thm ("EMPTY_COMPLETE",
  ``∀ r (mr : 'a MReg). [] ∈ language_of r ∧ is_marked_reg r mr ⇒ empty mr``,
  Induct >> Cases_on `mr` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (list_ss ++ SET_SPEC_ss) [empty, is_marked_reg, language_of, IN_SING]);

val MARK_LE_REFL = store_thm ("MARK_LE_REFL",
  ``∀ (r : 'a MReg). mark_le r r``,
  Induct >> ASM_REWRITE_TAC[mark_le]);

val MARK_LE_TRANS = store_thm ("MARK_LE_TRANS",
  ``∀ r s (t : 'a MReg). mark_le r s ∧ mark_le s t ⇒ mark_le r t``,
  Induct >> Cases_on `s` >> Cases_on `t` >>
  ASM_REWRITE_TAC [mark_le] >> METIS_TAC []);

val EMPTY_LE = store_thm ("EMPTY_LE",
  ``∀ r (s : 'a MReg). mark_le r s ⇒ (empty r = empty s)``,
  Induct >> Cases_on `s` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC bool_ss[mark_le, empty] >>
  METIS_TAC[]);

val FINAL_LE = store_thm ("FINAL_LE",
  ``∀ r (s : 'a MReg). mark_le r s ∧ final r ⇒ final s``,
  Induct >> Cases_on `s` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC bool_ss[mark_le, final] >>
  METIS_TAC [EMPTY_LE]);

val SHIFT_LE = store_thm ("SHIFT_LE",
  ``∀ r s (c : 'a) b1 b2.
      (b1 ⇒ b2) ⇒ (mark_le r s) ⇒ mark_le (shift b1 r c) (shift b2 s c)``,
  Induct >> Cases_on `s` >> REPEAT STRIP_TAC >> FULL_SIMP_TAC bool_ss[shift, mark_le] >>
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
  FULL_SIMP_TAC bool_ss [is_marked_reg, mark_reg, mark_le]);

val IS_MARKED_REG_LE = store_thm ("IS_MARKED_REG_LE",
  ``∀ r mr (ms : 'a MReg). is_marked_reg r mr ∧ mark_le mr ms ⇒ is_marked_reg r ms``,
  Induct >> Cases_on `mr` >> Cases_on `ms` >>
  ASM_SIMP_TAC bool_ss [is_marked_reg, mark_le] >>
  METIS_TAC []);

(** Equivalence with language **)

val ACCEPTM_ALT = store_thm ("ACCEPTM_ALT",
  ``∀ p q (li : 'a list). (acceptM p li ∨ acceptM q li) ⇒ acceptM (MAlt p q) li``,
  NTAC 3 STRIP_TAC >>
  FULL_SIMP_TAC bool_ss [acceptM] >>
  `∃ mp mq b.
    (FOLDL (shift F) (MInit T p) li = MInit b mp) ∧
    (FOLDL (shift F) (MInit T q) li = MInit b mq) ∧
    (FOLDL (shift F) (MInit T (MAlt p q)) li = MInit b (MAlt mp mq))` by (
    ID_SPEC_TAC ``li : 'a list`` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      METIS_TAC [MARK_LE_REFL],
      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [shift, FOLDL_SNOC] >>
      RW_TAC (bool_ss ++ QI_ss) [SHIFT_LE]
    ]) >>
  METIS_TAC [final, empty]);

val ACCEPTM_REP_APPEND = prove (
  ``∀ r x (y : 'a list).
    acceptM (MRep (mark_reg r)) x ∧ acceptM (mark_reg r) y ⇒
      acceptM (MRep (mark_reg r)) (x ++ y)``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC list_ss [acceptM, FOLDL_APPEND] >>

  `∃ mr b. mark_le (mark_reg r) mr ∧
    (FOLDL (shift F) (MInit T (MRep (mark_reg r))) x = MInit b (MRep mr))` by (
    ID_SPEC_TAC ``x : 'a list`` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      METIS_TAC [MARK_LE_REFL],

      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [shift, FOLDL_SNOC] >>
      METIS_TAC [MARK_REG_LE, SHIFT_IS_MARKED, MARK_IS_MARKED, IS_MARKED_REG_LE]
    ]) >>

  FULL_SIMP_TAC list_ss [] >>
  WEAKEN_TAC is_eq >>

  `∃ mr2 b2 mr3 b3. mark_le mr3 mr2 ∧ (b3 ⇒ b2 ∨ final mr2) ∧
    (FOLDL (shift F) (MInit T (mark_reg r)) y = (MInit b3 mr3)) ∧
    (FOLDL (shift F) (MInit b (MRep mr)) y = MInit b2 (MRep mr2))` by (
    ID_SPEC_TAC ``y : 'a list`` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      METIS_TAC [final],

      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [shift, FOLDL_SNOC] >>
      REPEAT (WEAKEN_TAC is_eq) >>
      RW_TAC (bool_ss ++ QI_ss) [] >>
      ASM_SIMP_TAC bool_ss [SHIFT_LE]
      (* It's odd that METIS isn't able to deal with this *)
    ]) >>

  METIS_TAC [final, empty, FINAL_LE]);

val ACCEPTM_REP = prove (
  ``∀ r (li : 'a list list).
    (∀ x. MEM x li ⇒ acceptM (mark_reg r) x) ⇒
      acceptM (MRep (mark_reg r)) (FLAT li)``,
  STRIP_TAC >>
  INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
    FULL_SIMP_TAC list_ss [acceptM, empty, final],
    FULL_SIMP_TAC list_ss [FLAT_SNOC, ACCEPTM_REP_APPEND]
  ]);

val ACCEPTM_SEQ = prove (
  ``∀ ra rb x (y : 'a list).
    acceptM (mark_reg ra) x ∧ acceptM (mark_reg rb) y ⇒
      acceptM (MSeq (mark_reg ra) (mark_reg rb)) (x ++ y)``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC list_ss [acceptM, FOLDL_APPEND] >>

  `∃ ma mb b. mark_le (mark_reg ra) ma ∧ mark_le (mark_reg rb) mb ∧
    (FOLDL (shift F) (MInit T (mark_reg ra)) x = MInit b ma) ∧
    (FOLDL (shift F) (MInit T (MSeq (mark_reg ra) (mark_reg rb))) x = MInit b (MSeq ma mb))` by (
    ID_SPEC_TAC ``x : 'a list`` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      METIS_TAC [MARK_LE_REFL],

      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [FOLDL_SNOC, shift] >>
      REPEAT (WEAKEN_TAC is_eq) >>

      EXISTS_TAC ``shift b ma (x'' : 'a)`` >>
      EXISTS_TAC ``shift (b ∧ empty ma ∨ final (ma : 'a MReg)) mb (x'' : 'a)`` >>
      EXISTS_TAC ``F`` >>
      METIS_TAC [MARK_REG_LE, SHIFT_IS_MARKED, MARK_IS_MARKED, IS_MARKED_REG_LE]
    ]) >>

  FULL_SIMP_TAC list_ss [] >>
  REPEAT (WEAKEN_TAC is_eq) >>

  `∃ rb2 b2 ma2 mb2 b3. mark_le rb2 mb2 ∧ (b2 ⇒ b3 ∧ empty ma2 ∨ final ma2) ∧
    (FOLDL (shift F) (MInit T (mark_reg rb)) y = MInit b2 rb2) ∧
    (FOLDL (shift F) (MInit b (MSeq ma mb)) y = MInit b3 (MSeq ma2 mb2))` by (
    ID_SPEC_TAC ``y : 'a list`` >>
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
      ASM_SIMP_TAC list_ss [] >>
      RW_TAC (bool_ss ++ QI_ss) [] >>
      FULL_SIMP_TAC bool_ss [final],

      STRIP_TAC >>
      FULL_SIMP_TAC list_ss [FOLDL_SNOC, shift] >>
      REPEAT (WEAKEN_TAC is_eq) >>

      RW_TAC (bool_ss ++ QI_ss) [SHIFT_LE]
    ]) >>

  METIS_TAC [final, empty, FINAL_LE, EMPTY_LE]);

val LANG_IN_ACCEPTM = prove (
  ``∀ (r : 'a Reg) w. w ∈ (language_of r) ⇒ acceptM (mark_reg r) w``,
  Induct >>
  FULL_SIMP_TAC bool_ss [mark_reg, is_marked_reg, language_of] >>
  REPEAT STRIP_TAC >| [
    FULL_SIMP_TAC list_ss [IN_SING, acceptM, empty, final],
    FULL_SIMP_TAC list_ss [IN_SING, acceptM, empty, final, shift],
    FULL_SIMP_TAC list_ss [IN_UNION, ACCEPTM_ALT],
    FULL_SIMP_TAC set_ss [ACCEPTM_SEQ],
    FULL_SIMP_TAC set_ss [ACCEPTM_REP]
  ]);

val ACCEPTM_SEQ_SOUND = store_thm ("ACCEPTM_SEQ_SOUND",
  ``∀ w b mr (r : 'a Reg).
  final (FOLDL (shift F) (MInit b (MSeq mr (mark_reg r))) w) ⇒
    ∃ x y. (w = x ++ y) ∧
      final (FOLDL (shift F) (MInit b mr) x) ∧
      acceptM (mark_reg r) y``,
  cheat);

val ACCEPTM_IN_LANG = prove (
  ``∀ (r : 'a Reg) w. acceptM (mark_reg r) w ⇒ w ∈ (language_of r)``,
  Induct >>
  FULL_SIMP_TAC bool_ss [language_of, IN_SING] >>
  REPEAT STRIP_TAC >| [
    cheat,
    cheat,
    cheat,
    cheat,
    cheat
  ]);

val ACCEPTM_CORRECT = store_thm ("ACCEPTM_CORRECT",
  ``∀ (r : 'a Reg) w. acceptM (mark_reg r) w ⇔ w ∈ (language_of r)``,
  REPEAT STRIP_TAC >>
  EQ_TAC >>
  REWRITE_TAC [ACCEPTM_IN_LANG, LANG_IN_ACCEPTM]);

val _ = export_theory();
