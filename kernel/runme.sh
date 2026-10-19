#!/bin/sh
kernel=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
if ! (cd "$kernel" && go build -o "$work/engine" .); then
	rm -rf "$work"
	exit 2
fi
"$work/engine" "$@"
status=$?
rm -rf "$work"
exit $status
