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

val _ = Datatype `MReg = MEps | MSym bool 'a | MAlt MReg MReg | MSeq MReg MReg | MRep MReg`;

(** Optimized-but-uncached regex matcher. **)

val empty = Define `
  (empty MEps = T) ∧
  (empty (MSym _ (_ : 'a)) = F) ∧
  (empty (MAlt p q) = empty p ∨ empty q) ∧
  (empty (MSeq p q) = empty p ∧ empty q) ∧
  (empty (MRep r) = T) `;

val final = Define `
  (final MEps = F) ∧
  (final (MSym b (_ : 'a)) = b) ∧
  (final (MAlt p q) = final p ∨ final q) ∧
  (final (MSeq p q) = (final p ∧ empty q) ∨ final q) ∧
  (final (MRep r) = final r) `;

val shift = Define `
  (shift _ MEps _ = MEps) ∧
  (shift m (MSym _ x) c = MSym (m ∧ (x = c)) x) ∧
  (shift m (MAlt p q) c = MAlt (shift m p c) (shift m q c)) ∧
  (shift m (MSeq p q) c = MSeq (shift m p c) (shift ((m ∧ empty p) ∨ final p) q c)) ∧
  (shift m (MRep r) c = MRep (shift (m ∨ final r) r c)) `;

val acceptM = Define `
  (acceptM r ([] : 'a list) = empty r) ∧
  (acceptM r (c :: cs) = final (FOLDL (shift F) (shift T r c) cs)) `;

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
  (mark_le _ _ = F) `;

val accept2 = Define `accept2 r l = acceptM (mark_reg r) l`;

(** Some tests **)

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

val ACCEPT_ALT_WEAKENING1 = store_thm ("ACCEPT_ALT_WEAKENING1",
  ``∀ p q (li : 'a list). acceptM p li ⇒ acceptM (MAlt p q) li``,
  cheat);

val ACCEPT_ALT_WEAKENING2 = store_thm ("ACCEPT_ALT_WEAKENING2",
  ``∀ p q (li : 'a list). acceptM q li ⇒ acceptM (MAlt p q) li``,
  cheat);

val EMPTY_SOUND = store_thm ("EMPTY_SOUND",
  ``∀ r (mr : 'a MReg). empty mr ∧ is_marked_reg r mr ⇒ [] ∈ language_of r``,
  cheat);

val EMPTY_COMPLETE = store_thm ("EMPTY_COMPLETE",
  ``∀ r (mr : 'a MReg). [] ∈ language_of r ∧ is_marked_reg r mr ⇒ empty mr``,
  cheat);

val ACCEPT_SEQ_EMPTY1 = store_thm ("ACCEPT_SEQ_EMPTY1",
  ``∀ p q (li : 'a list). empty p ∧ acceptM q li ⇒ acceptM (MSeq p q) li``,
  cheat);

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
  ``∀ r (s : 'a MReg). mark_le r s ⇒ final r ⇒ final s``,
  Induct >> Cases_on `s` >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC bool_ss[mark_le, final] >>
  METIS_TAC [EMPTY_LE]);

val FINAL_LE = store_thm ("FINAL_LE",
  ``∀ r (s : 'a MReg). mark_le r s ⇒ final r ⇒ final s``,
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

(** Equivalence with language **)

val ACCEPTM_IN_LANG = prove (
  ``∀ (r : 'a Reg) w. acceptM (mark_reg r) w ⇒ w ∈ (language_of r)``,
  cheat);

val LANG_IN_ACCEPTM = prove (
  ``∀ (r : 'a Reg) w. w ∈ (language_of r) ⇒ acceptM (mark_reg r) w``,

  `∀ (r : 'a Reg) mr w.
    w ∈ (language_of r) ∧ is_marked_reg r mr ⇒ acceptM mr w`
      suffices_by METIS_TAC[MARK_IS_MARKED] >>

  Induct >> Cases_on `mr` >>
  FULL_SIMP_TAC bool_ss [is_marked_reg, language_of] >>
  REPEAT STRIP_TAC >| [
    (* Eps *)
    Cases_on `w` >>
    FULL_SIMP_TAC list_ss [IN_SING, acceptM, empty],

    (* Sym *)
    Cases_on `w` >>
    FULL_SIMP_TAC list_ss [IN_SING, acceptM, empty, final, shift],

    (* Alt *)
    FULL_SIMP_TAC list_ss [IN_UNION] >>
    METIS_TAC [ACCEPT_ALT_WEAKENING1, ACCEPT_ALT_WEAKENING2],

    (* Seq *)
    (* XXX rename1 *)
    Q.RENAME1_TAC `acceptM (MSeq mp mq) w` >>
    Q.RENAME1_TAC `is_marked_reg p mp` >>
    Q.RENAME1_TAC `is_marked_reg q mq` >>
    FULL_SIMP_TAC set_ss [] >>
    Cases_on `x` >| [
      FULL_SIMP_TAC list_ss [] >>
      `empty mp` by METIS_TAC [EMPTY_COMPLETE] >>
      `acceptM mq y` by ASM_SIMP_TAC bool_ss [] >>
      ASM_SIMP_TAC bool_ss [ACCEPT_SEQ_EMPTY1],

      `acceptM mp (h::t)` by ASM_SIMP_TAC bool_ss [] >>
      FULL_SIMP_TAC list_ss [acceptM, FOLDL_APPEND] >>

      (* Step 1: the first FOLDL over t is accepted by the left half *)
      `∃ mq2. (FOLDL (shift F) (shift T (MSeq mp mq) h) t =
        MSeq (FOLDL (shift F) (shift T mp h) t) mq2) ∧
            is_marked_reg q mq2`
        by (
          ID_SPEC_TAC ``(t : 'a list)`` >>
          INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
            REPEAT STRIP_TAC >>
            ASM_SIMP_TAC list_ss [shift] >>
            EXISTS_TAC ``shift (empty (mp : 'a MReg) ∨ final mp) mq (h : 'a)`` >>
            ASM_SIMP_TAC bool_ss [SHIFT_IS_MARKED],

            REPEAT STRIP_TAC >>
            FULL_SIMP_TAC list_ss [shift, FOLDL_SNOC] >>
            EXISTS_TAC ``shift (final (FOLDL (shift F) (shift T mp (h : 'a)) t')) (mq2 : 'a MReg) x`` >>
            ASM_SIMP_TAC list_ss [SHIFT_IS_MARKED]
          ]) >>

      (* Step 1.5: Clean up remains of step 1 -- the left half is now irrelevant *)
      (* XXX Use Q.ABBREV_TAC *)
      FULL_SIMP_TAC bool_ss [] >>
      `acceptM mq2 y` by ASM_SIMP_TAC bool_ss [] >>

      `∃ half. FOLDL (shift F) (shift T mp h) t = half` by ASM_SIMP_TAC bool_ss [] >>
      FULL_SIMP_TAC bool_ss [] >>
      REPEAT (WEAKEN_TAC is_eq) >>
      REPEAT (WEAKEN_TAC is_forall) >>
      REPEAT (WEAKEN_TAC is_IN) >>
      REPEAT (WEAKEN_TAC (has_subterm
        (equal ``is_marked_reg : 'a Reg -> 'a MReg -> bool``))) >>

      (* Step 2: the second FOLDL over y is accepted by the right half *)
      Cases_on `y` >| [
        FULL_SIMP_TAC list_ss [final, shift, acceptM],

        FULL_SIMP_TAC list_ss [final, shift, acceptM] >>
        WEAKEN_TAC (equal ``final (half : 'a MReg)``) >>

        Q.ABBREV_TAC `mp = shift F half h` >>
        `∃ mp2 mq3. (FOLDL (shift F) (MSeq mp (shift T mq2 h)) t =
          MSeq mp2 mq3) ∧ mark_le (FOLDL (shift F) (shift T mq2 h) t) mq3`
          suffices_by METIS_TAC[final, FINAL_LE] >>

        REPEAT (WEAKEN_TAC (K true)) >>

        ID_SPEC_TAC ``(t : 'a list)`` >>
        INDUCT_THEN SNOC_INDUCT ASSUME_TAC >| [
          FULL_SIMP_TAC list_ss [] >>
          EXISTS_TAC ``mp : 'a MReg`` >>
          EXISTS_TAC ``(shift T mq2 h) : 'a MReg`` >>
          FULL_SIMP_TAC list_ss [MARK_LE_REFL],

          STRIP_TAC >>
          FULL_SIMP_TAC list_ss [shift, FOLDL_SNOC] >>
          EXISTS_TAC ``(shift F mp2 x) : 'a MReg`` >>
          EXISTS_TAC ``(shift (final (mp2 : 'a MReg)) mq3 x) : 'a MReg`` >>
          METIS_TAC [MARK_LE_TRANS, SHIFT_LE]
        ]
      ]
    ],

    (* Rep *)
    cheat
  ]);

val ACCEPTM_CORRECT = store_thm ("ACCEPTM_CORRECT",
  ``∀ (r : 'a Reg) w. acceptM (mark_reg r) w ⇔ w ∈ (language_of r)``,
  REPEAT STRIP_TAC >>
  EQ_TAC >>
  REWRITE_TAC [ACCEPTM_IN_LANG, LANG_IN_ACCEPTM]);

val _ = export_theory();
