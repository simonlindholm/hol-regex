
open RegexLib;

fun selftest (optMatcher : Matcher option) : unit = let
  fun test name matcher = let
    fun check reg str expected =
      if matches matcher (parseRegex reg) str = expected
      then ()
      else print ("TEST FAILED: Regex " ^ reg ^ " should " ^
          (if expected then "" else "not ") ^
          "match string \"" ^ str ^ "\"\n")
    val divby3 = "((0|3|6|9)|((1|4|7)(0|3|6|9)*(2|5|8))|(((2|5|8)|(1|4|7)(0|3|6|9)*(1|4|7))((0|3|6|9)*|(2|5|8)(0|3|6|9)*(1|4|7))((1|4|7)|(2|5|8)(0|3|6|9)*(2|5|8))))*"
  in (
    print ("Testing " ^ name ^ "...\n");
    (* eps *)
    check "" "" true;
    check "" "a" false;
    (* sym *)
    check "a" "a" true;
    check "a" "" false;
    check "a" "aa" false;
    (* seq *)
    check "aa" "aa" true;
    check "aa" "a" false;
    check "aa" "aaa" false;
    check "a()" "a" true;
    check "a()" "" false;
    check "a()" "aa" false;
    (* alt *)
    check "a|b" "a" true;
    check "a|b" "b" true;
    check "a|b" "ab" false;
    check "ab|a" "a" true;
    check "ab|a" "ab" true;
    check "ab|a" "b" false;
    (* rep *)
    check "a*" "" true;
    check "a*" "a" true;
    check "a*" "aa" true;
    check "a*" "b" false;
    check "a*" "ab" false;
    (* more complex tests *)
    check "a*ba*" "aba" true;
    check "a*aaaa*" "aa" false;
    check "a*aaaa*" "aaa" true;
    check "(a|b)*" "aba" true;
    check "(aa|bb)*" "aabbaa" true;
    check "(aa|bb)*" "abbaaa" false;
    check "(aa|)*" "aa" true;
    check "a(aa|)*a" "aa" true;
    check "a(aa|)*a" "aaaa" true;
    check "a(aa|)*a" "aaaa" true;
    check divby3 "0" true;
    check divby3 "1" false;
    check divby3 "3" true;
    check divby3 "123" true;
    check divby3 "124" false;
    check divby3 "125" false;
    check divby3 "126" true;
    check divby3 "127" false;
    check divby3 "3213" true;
    check divby3 "3214" false;
    print "done\n"
  )
  end
in
  case optMatcher of
       SOME m => test "given matcher" m
     | NONE => (
         test "SlowMatcher" SlowMatcher;
         test "FasterMatcher" FasterMatcher;
         test "FastestMatcher" FastestMatcher;
         test "BuiltinMatcher" BuiltinMatcher
       )
end

fun repl (optMatcher: Matcher option, str : string) : unit = let
  val re = parseRegex str
    handle e as (SyntaxError(msg)) => (print ("Syntax error: " ^ msg ^ "\n"); raise e)

  val matcher = getOpt (optMatcher, FastestMatcher)

  fun removeNl str =
    if String.isSuffix "\n" str
    then substring(str, 0, size str - 1)
    else str

  fun test str =
    if matches matcher re (removeNl str)
      then print str
      else ()

  fun loop() =
    case (TextIO.inputLine TextIO.stdIn)
      of SOME line => (test line; loop())
       | NONE => ()
in
  loop()
end

fun main () = let
  val matcher = ref (NONE: Matcher option)
  fun parseMatcher "slow" = SOME SlowMatcher
    | parseMatcher "faster" = SOME FasterMatcher
    | parseMatcher "fastest" = SOME FastestMatcher
    | parseMatcher "builtin" = SOME BuiltinMatcher
    | parseMatcher str =
        (print ("Warning: unrecognized matcher \"" ^ str ^ "\"\n"); NONE)

  val args = CommandLine.arguments()
  val args2 = if not (null args) andalso String.isPrefix "--matcher=" (hd args)
              then (matcher := parseMatcher (String.extract (hd args, 10, NONE)); tl args)
              else args
in
  case args2 of
       [] => selftest (!matcher)
     | [str] => repl (!matcher, str)
     | _ => print ("Usage: ./test [--matcher=slow|faster|fastest|builtin] [regex]\n")
end
