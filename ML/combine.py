#!/usr/bin/env python3
import subprocess
import sys

if len(sys.argv) != 2:
    print("Usage: python3 combine.py <base name>")
    exit(1)

holdir = str(subprocess.check_output(["./holdir.sh"]), 'utf-8')

out = []
handled = set()
def rec(path):
    # XXX We are trying to avoid the overlay, but still want to use
    # regexpMatch, which depends on it. Replace its dependency by the
    # primitives it really uses.
    if "Overlay" in path:
        rec("$(HOLDIR)/tools-poly/poly/Binaryset")
        rec("$(HOLDIR)/tools-poly/poly/Binarymap")
        rec("$(HOLDIR)/tools-poly/poly/Listsort")
        return

    path = path.replace('$(HOLDIR)', holdir)
    if path in handled:
        return
    handled.add(path)
    if path.endswith('.sig') or path.endswith('.sml'):
        out.append(path)
    elif path.endswith('.ui') or path.endswith('.uo'):
        try:
            with open(path) as f:
                lines = [line.strip() for line in f]
        except:
            # missing files are okay
            return
        for line in lines:
            rec(line.strip())
    else:
        rec(path + '.ui')
        rec(path + '.uo')

res = []

# Annoyingly, some of the built-in ML files depend on PP, which usually comes
# from the overlay. Substitute our own prelude.
rec("$(HOLDIR)/src/portableML/HOLPP")
for script in out:
    res.append('use "{}";'.format(script))
res.append("structure PP = HOLPP;")
res.append("type ppstream = PP.ppstream;")
res.append("")
out = []

rec(sys.argv[1])
for script in out:
    res.append('use "{}";'.format(script))

for line in res:
    print(line)
