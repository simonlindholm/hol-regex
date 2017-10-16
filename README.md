# hol-regex

This repo contains a simple, formally verified implementation of a regex engine in Standard ML.
The formal verification is done using [HOL](https://hol-theorem-prover.org/), with code auto-generated from HOL definitions using the EmitML library.
This project was done as part of an interactive theorem proving course at KTH, and is not likely to be of much practical use.

The regex engine is based on the very nice paper *A Play on Regular Expressions* by Sebastian Fischer, Frank Huch and Thomas Wilke, published at ICFP 2010 (http://www-ps.informatik.uni-kiel.de/~sebf/pub/regexp-play.html).

## Build instructions

Ensure that you have HOL and PolyML installed.
Then `cd` into the `ML/` directory, and type `Holmake`.

This should emit code for a regex implementation, `regexML.{sig,sml}`,
and compile a test program `test` (from `test.sml`) that uses this as a library.
The test program works roughly like `grep`: `./test regex < file` prints all the lines of `file` that match the regex (fully; not just contain a matching substring).
