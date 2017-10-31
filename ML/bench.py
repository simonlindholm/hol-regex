import math
import time
import subprocess

matchers = ['slow', 'faster', 'fastest', 'builtin']

def run(matcher, regex, inp):
    args = ["./test", "--matcher=" + matcher, regex]
    with subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.DEVNULL) as p:
        try:
            p.communicate(input=bytes(inp, 'utf-8'), timeout=6)
        except subprocess.TimeoutExpired as e:
            p.kill()
            raise e

def bench(matcher, regex, inp):
    try:
        min_time = 0.2
        inp += "\n"
        t0 = time.time()
        run(matcher, regex, inp)
        t1 = time.time()
        dur = t1 - t0
        repeats = math.floor(min_time / dur)
        if repeats <= 1:
            return dur
        inp *= (repeats - 1)
        run(matcher, regex, inp)
        t1 = time.time()
        dur = t1 - t0
        return dur / repeats
    except subprocess.TimeoutExpired:
        return None

def print_table(desc, ns, fn):
    table = []
    for matcher in matchers:
        times = []
        stop = False
        lastn = -1
        for n in ns:
            if not stop and times and times[-1] * n / lastn >= 2.0:
                # would be too slow to run, assuming linear growth
                stop = True
            lastn = n
            if stop:
                times.append(None)
            else:
                r,i = fn(n)
                times.append(bench(matcher, r, i))
                if times[-1] is None:
                    stop = True
        table.append(times)

    print("Benchmark: " + desc)
    print("---------------")
    topleft = "n \\ matcher"
    print(topleft + " | " + " | ".join(m.rjust(10) for m in matchers))
    for i, n in enumerate(ns):
        res = []
        for m in range(len(matchers)):
            val = table[m][i]
            name = matchers[m]
            s = "-" if val is None else "{:.2}".format(val)
            res.append(s.rjust(10))
        print(str(n).ljust(len(topleft)) + "   " + "   ".join(res))
    print("---------------")
    print()


def tc1(n):
    return ('aa*aa', 'a' * n)
print_table("|aa*aa| vs |a^n|", [10, 20, 30, 100, 1000, 10**4, 10**5, 10**6, 10**7], tc1)

def tc2(n):
    return ('a' + '(a|b)' * n + 'a', 'a' * (n+2))
print_table("|a (a|b)^n a| vs |a^(n+2)|", [10, 30, 100, 300, 1000, 3000, 10000], tc2)

def tc3(n):
    return ('a*' * n + 'a', 'a' * 10)
print_table("|(a*)^n a| vs |a^10|", [10, 100, 1000, 10**4, 3*10**4], tc3)
