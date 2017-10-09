#!/bin/bash
set -e
echo 'PolyML.print_depth 0;' > .temp
python3 combine.py "$1" >> .temp
echo 'PolyML.print_depth 10;' >> .temp
rlwrap poly -q --use .temp
rm .temp
