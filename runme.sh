cd "$(dirname "$0")" || exit 2
machine="$(mktemp)" || exit 2
go build -o "$machine" . || exit 2
"$machine" spec.plain
answer=$?
rm -f "$machine"
exit "$answer"
