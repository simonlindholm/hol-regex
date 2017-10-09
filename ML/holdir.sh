#!/bin/bash

if [ -z "$HOLDIR" ]; then
	X=$(which hol)
	HOLDIR=${X%/bin/hol}
fi
echo -n "$HOLDIR"
