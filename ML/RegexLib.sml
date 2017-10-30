structure RegexLib :> RegexLib =
struct
  datatype Regex
       = Eps
       | Sym of char
       | Alt of Regex * Regex
       | Seq of Regex * Regex
       | Rep of Regex

  type Matcher = Regex -> string -> bool

  exception SyntaxError of string

  fun regexToCharReg Eps = regexML.Eps
    | regexToCharReg (Sym c) = regexML.Sym c
    | regexToCharReg (Alt(p, q)) = regexML.Alt (regexToCharReg p, regexToCharReg q)
    | regexToCharReg (Seq(p, q)) = regexML.Seq (regexToCharReg p, regexToCharReg q)
    | regexToCharReg (Rep r) = regexML.Rep (regexToCharReg r)

  fun SlowMatcher (re : Regex) (str : string) : bool =
    regexML.accept (regexToCharReg re) (explode str)

  fun FasterMatcher (re : Regex) (str : string) : bool =
    regexML.accept2 (regexToCharReg re) (explode str)

  fun FastestMatcher (re : Regex) (str : string) : bool =
    regexML.accept3 (regexToCharReg re) (explode str)

  fun regexToBuiltin Eps = regexpMatch.Epsilon
    | regexToBuiltin (Sym c) = regexpMatch.Symbs (regexpMatch.pred_to_set (fn d => d = c))
    | regexToBuiltin (Alt(p, q)) = regexpMatch.Sum (regexToBuiltin p, regexToBuiltin q)
    | regexToBuiltin (Seq(p, q)) = regexpMatch.Dot (regexToBuiltin p, regexToBuiltin q)
    | regexToBuiltin (Rep r) = regexpMatch.Star (regexToBuiltin r)

  fun BuiltinMatcher (re : Regex) (str : string) : bool =
    regexpMatch.match (regexToBuiltin re) str

  fun parseRegex (input : string) : Regex = let
    val len = size input
    val pos = ref 0

    fun peek() = if (!pos) = len then Char.minChar else String.sub(input, !pos)

    fun eat() : char =
      (pos := (!pos) + 1;
      String.sub(input, (!pos) - 1))

    fun expect (ch : char) : unit = (
      if (!pos) = len then raise SyntaxError
          ("expected " ^ str ch ^ ", found EOF") else ();
      if String.sub(input, !pos) <> ch then raise SyntaxError
          ("expected " ^ str ch ^ ", found " ^ substring(input, !pos, 1)) else ();
      pos := (!pos) + 1; ())

    fun expectEOF() : unit =
      if (!pos) <> len then raise SyntaxError
          ("expected EOF, found " ^ substring(input, !pos, 1)) else ()

    fun moreAtoms (ch : char) : bool =
      (ch <> #"\^@" andalso ch <> #")" andalso ch <> #"|" andalso ch <> #"*")

    fun parseAlt() : Regex = let
      val a = parseSeq()
    in
      if peek() = #"|" then (expect #"|"; Alt(a, parseAlt()))
      else a
    end

    and parseSeq() : Regex =
      if moreAtoms (peek()) then parseNonEmptySeq()
      else Eps

    and parseNonEmptySeq() : Regex = let
      val a = parseRep()
    in
      if moreAtoms (peek()) then
        Seq(a, (parseNonEmptySeq()))
      else a
    end

    and parseRep() : Regex = addStars (parseAtom())

    and addStars (re : Regex) : Regex =
      if peek() = #"*" then (expect #"*"; addStars (Rep(re)))
      else re

    and parseAtom() : Regex = let
      val ch = eat()
    in
      if ch = #"(" then parseAlt() before expect #")"
      else Sym(ch)
    end

  in
    parseAlt() before expectEOF()
  end

  fun matches (m : Matcher) (re : Regex) (str : string) : bool = m re str

end
