#!/bin/bash
POLY=/usr/bin/poly
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

HOLDIR=$("$DIR/holdir.sh")
BIN="$HOLDIR/bin"

if [ -z "$HEAP" ]; then
	HEAP=$("$BIN/heapname")
fi

"$POLY" -q --use "$BIN/hol.ML" --gcthreads=1 "$HEAP" \
	<("$BIN/unquote" < "$1") </dev/null
