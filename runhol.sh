#!/bin/bash
POLY=/usr/bin/poly

if [ -z "$HOLDIR" ]; then
	X=$(which hol)
	HOLDIR=${X%/bin/hol}
fi
BIN="$HOLDIR/bin"

if [ -z "$HEAP" ]; then
	HEAP=$("$BIN/heapname")
fi

"$POLY" -q --use "$BIN/hol.ML" --gcthreads=1 "$HEAP" \
	<("$BIN/unquote" < "$1") </dev/null
