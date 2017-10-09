#!/bin/bash
POLY=/usr/bin/poly
DIR=$(dirname "$(readlink -f "$0")")

HOLDIR=$("$DIR/holdir.sh")
BIN="$HOLDIR/bin"

if [ -z "$HEAP" ]; then
	HEAP=$("$BIN/heapname")
fi

"$POLY" -q --use "$BIN/hol.ML" --gcthreads=1 "$HEAP" \
	<("$BIN/unquote" < "$1") </dev/null
