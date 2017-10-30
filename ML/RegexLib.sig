signature RegexLib =
sig
  datatype Regex
       = Eps
       | Sym of char
       | Alt of Regex * Regex
       | Seq of Regex * Regex
       | Rep of Regex

  type Matcher

  val SlowMatcher : Matcher
  val FasterMatcher : Matcher
  val FastestMatcher : Matcher
  val BuiltinMatcher : Matcher

  exception SyntaxError of string

  (* Parse a string into a regex. The string should follow this grammar:
   *
   * regex = part ("|" part)*
   * part = (atom "*"* )*
   * atom = "(" regex ")" | char
   * char = any character except "*", "(", ")", "|"
   *
   * If it does not, a SyntaxError is thrown.
   *)
  val parseRegex : string -> Regex

  val matches : Matcher -> Regex -> string -> bool
end
