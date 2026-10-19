#!/bin/sh
machine=$(cd "$(dirname "$0")" && pwd) || exit 2
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd "$machine" && go build -o "$work/engine" .) >&2 || exit 2
"$work/engine" "$machine"
