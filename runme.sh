cd "$(dirname "$0")" || exit 2
place=$(mktemp -d) || exit 2
trap 'rm -rf "$place"' EXIT
go build -buildvcs=false -o "$place/engine" . || exit 2
"$place/engine" "$@"
