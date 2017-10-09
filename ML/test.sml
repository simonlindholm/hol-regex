
open regexML;
open regexLib;

fun main () = let
  val args = CommandLine.arguments()
  val str = hd args
    handle Empty => (print "Usage: ./test regex\n"; raise Empty);
  val re = parseRegex str
    handle e as (SyntaxError(msg)) => (print ("Syntax error: " ^ msg ^ "\n"); raise e)

  fun removeNl str =
    if String.isSuffix "\n" str
    then substring(str, 0, size str - 1)
    else str

  fun test str =
    if accept re (explode (removeNl str))
      then print str
      else ()

  fun loop() =
    case (TextIO.inputLine TextIO.stdIn)
      of SOME line => (test line; loop())
        | NONE => ()
in
  print "GO!\n";
  loop()
end
