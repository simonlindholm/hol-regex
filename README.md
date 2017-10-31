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

Alternatively, `./test` without arguments runs a small self-test on the library.

## Performance

`bench.py` does some unscientific performance benchmarking of the three different algorithms
implemented by the library, and the built-in regex matcher (regexpMatch.sml) that comes with HOL.
Results vary quite a bit from run to run because of garbage collection and similar non-determinism,
but might still give some hint about real-world performance.

On my ~2015 era laptop I see the following performance measurements:

```
Benchmark: |aa*aa| vs |a^n|
---------------
n \ matcher |       slow |     faster |    fastest |    builtin
10                0.0007      0.00019      0.00018       0.0011
20                  0.32      0.00019      0.00018       0.0011
30                     -      0.00018      0.00055       0.0011
100                    -      0.00027      0.00026       0.0011
1000                   -      0.00045      0.00047       0.0018
10000                  -       0.0024       0.0035       0.0014
100000                 -        0.034        0.051       0.0026
1000000                -         0.43         0.48        0.021
10000000               -            -            -         0.18
---------------
```

(Short regex, long string. `slow` is terrible; `faster` and `fastest` are about equally good.
The `builtin` matcher is 10x faster, but still in the same ballpark.)

```
Benchmark: |a (a|b)^n a| vs |a^(n+2)|
---------------
n \ matcher |       slow |     faster |    fastest |    builtin
10               0.00014       0.0013      0.00017      0.00086
30                0.0003      0.00019      0.00029       0.0039
100                0.014      0.00076       0.0012        0.064
300                 0.78       0.0053       0.0096          1.2
1000                  29        0.071          0.1           43
3000                   -          0.5         0.77            -
10000                  -          4.8          8.4            -
---------------
```

(Long regex, long string. `slow` gets lucky and does surprisingly well. `faster` and `fastest` both cope pretty well, though `fastest` is slightly slower, probably due to generating more garbage.
`builtin` does reasonably up to a point, but is not well optimized for large regexes.)

```
Benchmark: |(a*)^n a| vs |a^10|
---------------
n \ matcher |       slow |     faster |    fastest |    builtin
10               0.00048      0.00028      0.00028       0.0032
100               0.0011      0.00028      0.00074         0.52
1000               0.012       0.0054       0.0018            -
10000               0.12         0.32         0.06            -
30000               0.67          2.7         0.37            -
---------------
```

(Long regex, short string. `slow` again gets lucky. `fastest` does asymptotically better than `faster` due to caching. As seen before, `builtin` does not cope well with long regexes.)
