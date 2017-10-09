signature regexLib =
sig

  exception SyntaxError of string;

  (* Parse a string into a char regex. The string should follow this grammar:
   *
   * regex = part ("|" part)*
   * part = (atom "*"* )*
   * atom = "(" regex ")" | char
   * char = any character except "*", "(", ")", "|"
   *
   * If it does not, a SyntaxError is thrown.
   *)
  val parseRegex : string -> char regexML.Reg

end
