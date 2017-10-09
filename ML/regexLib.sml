structure regexLib :> regexLib =
struct

  open regexML

  exception SyntaxError of string;

  fun parseRegex (input : string) : char Reg = let
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

    fun parseAlt() : char Reg = let
      val a = parseSeq()
    in
      if peek() = #"|" then (expect #"|"; Alt(a, parseAlt()))
      else a
    end

    and parseSeq() : char Reg =
      if moreAtoms (peek()) then parseNonEmptySeq()
      else Eps

    and parseNonEmptySeq() : char Reg = let
      val a = parseRep()
    in
      if moreAtoms (peek()) then
        Seq(a, (parseNonEmptySeq()))
      else a
    end

    and parseRep() : char Reg = addStars (parseAtom())

    and addStars (re : char Reg) : char Reg =
      if peek() = #"*" then (expect #"*"; addStars (Rep(re)))
      else re

    and parseAtom() : char Reg = let
      val ch = eat()
    in
      if ch = #"(" then parseAlt() before expect #")"
      else Sym(ch)
    end

  in
    parseAlt() before expectEOF()
  end

end
